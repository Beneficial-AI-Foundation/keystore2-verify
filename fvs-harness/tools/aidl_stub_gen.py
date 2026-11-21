#!/usr/bin/env python3
"""Generate the AIDL stand-in crates of fvs-harness from .aidl sources.

Python standard library only.

    python3 fvs-harness/tools/aidl_stub_gen.py            # write fvs-harness/aidl/<crate>/
    python3 fvs-harness/tools/aidl_stub_gen.py --check    # regenerate in memory, fail if a file differs

What it makes. Soong turns every aidl_interface into a Rust crate (android.hardware.security.keymint-V5
becomes the crate android_hardware_security_keymint). The code of keystore2 only needs those crates to
type-check, so each generated crate has the same item paths, field types, derives, enum representation
and trait signatures as the real one, and bodies that panic. Nothing here models behaviour: every
interface method is an assumption of the verification, not a proved fact.

The mapping of AIDL to Rust follows the AIDL compiler at the tag the inputs come from
(system/tools/aidl generate_rust.cpp and aidl_to_rust.cpp, android-17.0.0_r1):
  parcelable   struct with pub fields; derives Debug plus @RustDerive; Default written out
  union        enum, one variant per field, capitalised; Default is the first variant
  enum         binder::declare_binder_enum!, a newtype over the backing integer with constants
  interface    trait IFoo: binder::Interface + Send, module-level constants, BnFoo, BpFoo
  every type X in package a.b lives at  <crate>::aidl::a::b::X::X
Argument types: primitives and enums by value; String, arrays and List by slice (&str, &[T]);
everything else by reference; @nullable wraps in Option; out and inout arguments are &mut.
"""
import argparse
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
HARNESS = HERE.parent
REPO = HARNESS.parent

# crate name -> directories that hold its .aidl files (package trees). Inputs under aidl-src are
# fetched by fetch_aidl_inputs.py; the keystore2 ones are read in place.
SRC = HARNESS / "aidl-src"
CRATES = {
    "android_hardware_security_keymint": [SRC / "android.hardware.security.keymint-V5"],
    "android_hardware_security_secureclock": [SRC / "android.hardware.security.secureclock-V1"],
    "android_hardware_security_sharedsecret": [SRC / "android.hardware.security.sharedsecret-V1"],
    "android_hardware_security_rkp": [SRC / "android.hardware.security.rkp-V3"],
    "android_system_keystore2": [SRC / "android.system.keystore2-V6"],
    "android_security_rkp_aidl": [SRC / "android.security.rkp_aidl"],
    "android_os_permissions_aidl": [SRC / "android.os.permissions_aidl"],
    "apex_aidl_interface": [SRC / "apex_aidl_interface"],
    "packagemanager_aidl": [SRC / "packagemanager_aidl"],
    "android_security_apc": [REPO / "keystore2/aidl/android/security/apc"],
    "android_security_authorization": [REPO / "keystore2/aidl/android/security/authorization"],
    "android_security_compat": [REPO / "keystore2/aidl/android/security/compat"],
    "android_security_maintenance": [REPO / "keystore2/aidl/android/security/maintenance"],
    "android_security_metrics": [REPO / "keystore2/aidl/android/security/metrics"],
}

PRIMITIVES = {"boolean": "bool", "byte": "i8", "char": "u16", "int": "i32", "long": "i64",
              "float": "f32", "double": "f64"}
BUILTINS = {"String": "alloc::string::String", "IBinder": "binder::SpIBinder",
            "ParcelFileDescriptor": "binder::ParcelFileDescriptor"}
BACKING = {"byte": "i8", "int": "i32", "long": "i64"}


# ---------------------------------------------------------------- lexer
def lex(text):
    toks, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif text.startswith("//", i):
            i = text.find("\n", i)
            i = n if i < 0 else i
        elif text.startswith("/*", i):
            j = text.find("*/", i + 2)
            i = n if j < 0 else j + 2
        elif c == '"':
            j = i + 1
            while text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            toks.append(("str", text[i:j + 1]))
            i = j + 1
        elif c == "'":
            j = i + 1
            while text[j] != "'":
                j += 2 if text[j] == "\\" else 1
            toks.append(("chr", text[i:j + 1]))
            i = j + 1
        elif c.isalpha() or c == "_":
            m = re.compile(r"[A-Za-z_][A-Za-z0-9_]*").match(text, i)
            toks.append(("id", m.group()))
            i = m.end()
        elif c.isdigit():
            m = re.compile(r"0[xX][0-9a-fA-F]+[lL]?|\d+\.?\d*(?:[eE][-+]?\d+)?[fFlL]?").match(text, i)
            toks.append(("num", m.group()))
            i = m.end()
        elif text.startswith("<<", i):
            toks.append(("p", "<<"))
            i += 2
        else:
            toks.append(("p", c))
            i += 1
    return toks


# ---------------------------------------------------------------- model
class Type:
    def __init__(self, name, args, dims, ann):
        self.name, self.args, self.dims, self.ann = name, args, dims, ann  # dims: [None | int]

    @property
    def nullable(self):
        return "nullable" in self.ann

    @property
    def heap(self):
        return self.ann.get("nullable", "").replace(" ", "") == "heap=true"

    @property
    def is_array(self):
        return bool(self.dims)

    @property
    def is_list(self):
        return self.name == "List" and not self.dims


class Decl:
    def __init__(self, kind, name, pkg, ann, outer=None):
        self.kind, self.name, self.pkg, self.ann, self.outer = kind, name, pkg, ann, outer
        self.fields, self.consts, self.methods, self.enumerators, self.nested = [], [], [], [], []
        self.backing = "byte"
        self.imports, self.crate, self.structured = [], None, True

    @property
    def full(self):
        return (self.outer.full if self.outer else self.pkg) + "." + self.name

    @property
    def derives(self):
        a = self.ann.get("RustDerive", "")
        return [k for k, v in re.findall(r"(\w+)\s*=\s*(\w+)", a) if v == "true"]


class Parser:
    def __init__(self, toks, crate, src):
        self.t, self.i, self.crate, self.src = toks, 0, crate, src

    def peek(self, k=0):
        return self.t[self.i + k] if self.i + k < len(self.t) else ("eof", "")

    def next(self):
        tok = self.peek()
        self.i += 1
        return tok

    def eat(self, v):
        if self.peek()[1] == v:
            self.i += 1
            return True
        return False

    def expect(self, v):
        if not self.eat(v):
            raise SystemExit(f"{self.src}: expected {v!r}, found {self.peek()!r} (token {self.i})")

    def annotations(self):
        ann = {}
        while self.peek()[1] == "@":
            self.next()
            name = self.next()[1]
            while self.peek()[1] == "." and self.peek(1)[0] == "id":
                self.next()
                name = self.next()[1]
            args = ""
            if self.peek()[1] == "(":
                depth, parts = 0, []
                while True:
                    k, v = self.next()
                    if v == "(":
                        depth += 1
                        if depth == 1:
                            continue
                    if v == ")":
                        depth -= 1
                        if depth == 0:
                            break
                    parts.append(v)
                args = " ".join(parts)
            ann[name] = args
        return ann

    def qname(self):
        n = self.next()[1]
        while self.peek()[1] == "." and self.peek(1)[0] == "id":
            self.next()
            n += "." + self.next()[1]
        return n

    def parse_type(self, ann=None):
        ann = dict(ann or {})
        ann.update(self.annotations())
        name = self.qname()
        args = []
        if self.eat("<"):
            args.append(self.parse_type())
            while self.eat(","):
                args.append(self.parse_type())
            self.expect(">")
        dims = []
        while self.peek()[1] == "[":
            self.next()
            if self.peek()[1] == "]":
                dims.append(None)
            else:
                dims.append(int(self.next()[1]))
            self.expect("]")
        return Type(name, args, dims, ann)

    def expr_until(self, stops):
        depth, parts = 0, []
        while True:
            k, v = self.peek()
            if depth == 0 and v in stops:
                break
            if v in "([":
                depth += 1
            if v in ")]":
                depth -= 1
            parts.append((k, v))
            self.next()
        return parts

    def unit(self):
        pkg, imports, decls = "", [], []
        while self.peek()[0] != "eof":
            save = self.i
            ann = self.annotations()
            if self.peek()[1] == "package":
                self.next()
                pkg = self.qname()
                self.expect(";")
            elif self.peek()[1] == "import":
                self.next()
                imports.append(self.qname())
                self.expect(";")
            else:
                self.i = save
                decls.append(self.decl(pkg, None))
        for d in decls:
            self.tag(d, imports)
        return decls

    def tag(self, d, imports):
        d.imports, d.crate = imports, self.crate
        for n in d.nested:
            self.tag(n, imports)

    def decl(self, pkg, outer):
        ann = self.annotations()
        oneway = self.eat("oneway")
        kw = self.next()[1]
        if kw not in ("parcelable", "enum", "union", "interface"):
            raise SystemExit(f"{self.src}: unexpected {kw!r} at token {self.i}")
        d = Decl(kw, self.next()[1], pkg, ann, outer)
        if self.eat("<"):  # generic parcelable parameters
            while not self.eat(">"):
                self.next()
        if kw == "parcelable" and self.peek()[1] != "{":
            while not self.eat(";"):
                self.next()
            d.structured = False
            return d
        self.expect("{")
        if kw == "enum":
            if "Backing" in ann:
                d.backing = re.search(r'type\s*=\s*"(\w+)"', ann["Backing"]).group(1)
            while not self.eat("}"):
                self.annotations()
                name = self.next()[1]
                expr = None
                if self.eat("="):
                    expr = self.expr_until({",", "}"})
                self.eat(",")
                d.enumerators.append((name, expr))
            return d
        while not self.eat("}"):
            if self.peek()[1] in ("parcelable", "enum", "union", "interface") or (
                    self.peek()[1] == "@" and self.nested_decl_ahead()):
                d.nested.append(self.decl(pkg, d))
                continue
            mann = self.annotations()
            if self.peek()[1] == "const":
                self.next()
                ty = self.parse_type()
                name = self.next()[1]
                self.expect("=")
                d.consts.append((ty, name, self.expr_until({";"})))
                self.expect(";")
                continue
            mway = self.eat("oneway")
            if kw == "interface":
                ret = self.parse_type(mann)
                name = self.next()[1]
                self.expect("(")
                args = []
                while not self.eat(")"):
                    aann = self.annotations()
                    direction = "in"
                    if self.peek()[1] in ("in", "out", "inout"):
                        direction = self.next()[1]
                    aann.update(self.annotations())
                    ty = self.parse_type(aann)
                    args.append((direction, ty, self.next()[1]))
                    self.eat(",")
                if self.eat("="):
                    self.next()
                self.expect(";")
                d.methods.append((ret, name, args, mway or "oneway" in ann))
            else:
                ty = self.parse_type(mann)
                name = self.next()[1]
                default = None
                if self.eat("="):
                    default = self.expr_until({";"})
                self.expect(";")
                d.fields.append((ty, name, default))
        return d

    def nested_decl_ahead(self):
        j = self.i
        while self.t[j][1] == "@":
            j += 2
            if self.t[j][1] == "(":
                depth = 0
                while True:
                    if self.t[j][1] == "(":
                        depth += 1
                    if self.t[j][1] == ")":
                        depth -= 1
                        if depth == 0:
                            j += 1
                            break
                    j += 1
        return self.t[j][1] in ("parcelable", "enum", "union", "interface", "oneway")


# ---------------------------------------------------------------- registry and evaluation
class World:
    def __init__(self):
        self.decls = {}
        self.enum_cache = {}

    def add(self, d):
        if d.full in self.decls:
            raise SystemExit(f"duplicate AIDL type {d.full}")
        self.decls[d.full] = d
        for n in d.nested:
            self.add(n)

    def resolve(self, name, scope):
        """Find the Decl a type name in `scope` (a Decl) refers to, or None for a builtin."""
        if name in PRIMITIVES or name in BUILTINS or name in ("void", "List", "Map", "ParcelableHolder"):
            return None
        cands = [name]
        o = scope
        while o is not None:
            cands.append(f"{o.full}.{name}")
            o = o.outer
        cands += [i for i in scope.imports if i.endswith("." + name)]
        top = scope
        while top.outer:
            top = top.outer
        cands.append(f"{top.pkg}.{name}")
        for c in cands:
            if c in self.decls:
                return self.decls[c]
        raise SystemExit(f"cannot resolve type {name!r} used in {scope.full}")

    def enum_value(self, d, name):
        key = (d.full, name)
        if key not in self.enum_cache:
            nxt = 0
            bits = int(BACKING[d.backing][1:])
            for n, expr in d.enumerators:
                v = self.evaluate(expr, d) if expr else nxt
                # AIDL stores the value in the backing type: 4294967295 in an int enum is -1.
                v = (v + (1 << (bits - 1))) % (1 << bits) - (1 << (bits - 1))
                self.enum_cache[(d.full, n)] = v
                nxt = v + 1
        return self.enum_cache[key]

    def evaluate(self, parts, scope):
        """Evaluate a constant expression: integers, enumerators, strings, booleans, operators."""
        out = []
        i = 0
        while i < len(parts):
            k, v = parts[i]
            if k == "id" and v in ("true", "false"):
                out.append("True" if v == "true" else "False")
            elif k == "id":
                chain = [v]
                while i + 2 < len(parts) and parts[i + 1][1] == "." and parts[i + 2][0] == "id":
                    chain.append(parts[i + 2][1])
                    i += 2
                out.append(str(self.lookup(chain, scope)))
            elif k == "num":
                s = v.rstrip("lL") if v.lower().startswith("0x") else v.rstrip("lLfF")
                out.append(s)
            elif k == "str":
                out.append(repr(bytes(v[1:-1], "utf-8").decode("unicode_escape")))
            elif k == "chr":
                out.append(str(ord(v[1:-1])))
            else:
                out.append({"~": "~", "!": " not "}.get(v, v))
            i += 1
        return eval("".join(out), {"__builtins__": {}}, {})

    def lookup(self, chain, scope):
        if len(chain) == 1:  # a sibling enumerator or constant
            for n, expr in scope.enumerators:
                if n == chain[0]:
                    return self.enum_value(scope, n)
            for _, n, expr in scope.consts:
                if n == chain[0]:
                    return self.evaluate(expr, scope)
            raise SystemExit(f"cannot evaluate name {chain[0]!r} in {scope.full}")
        full = ".".join(chain[:-1])
        d = self.decls.get(full) or self.resolve(chain[-2] if len(chain) == 2 else full, scope)
        if len(chain) >= 2 and d is None:
            d = self.resolve(".".join(chain[:-1]), scope)
        if d.kind == "enum":
            return self.enum_value(d, chain[-1])
        for _, n, expr in d.consts:
            if n == chain[-1]:
                return self.evaluate(expr, d)
        raise SystemExit(f"cannot evaluate {'.'.join(chain)}")


# ---------------------------------------------------------------- emitter
KEYWORDS_NO_RAW = {"self", "Self", "super", "crate"}


def rid(n):
    return f"{n}_" if n in KEYWORDS_NO_RAW else f"r#{n}"


class Emitter:
    def __init__(self, world, crate):
        self.w, self.crate = world, crate
        self.deps = set()

    def path(self, d):
        if d.crate == self.crate:
            prefix = "crate"
        else:
            prefix = d.crate
            self.deps.add(d.crate)
        parts = d.pkg.split(".")
        chain, o = [], d
        while o is not None:
            chain.append(o.name)
            o = o.outer
        chain.reverse()
        mods = "::".join(rid(p) for p in parts)
        # Module X holds trait or struct X and the modules of the types nested in it:
        # X::X for a top-level type, X::Y::Y for Y nested in X.
        types = "::".join(rid(p) for p in chain + chain[-1:])
        return f"{prefix}::aidl::{mods}::{types}"

    def rust_type(self, t, mode, scope):
        """RustNameOf from aidl_to_rust.cpp. mode: VALUE FIELD IN UNSIZED OUT INOUT DEFAULT."""
        decl = self.w.resolve(t.name, scope)
        if t.is_array or t.is_list:
            el = t.args[0] if t.is_list else Type(t.name, t.args, [], {})
            if t.is_array and any(x is not None for x in t.dims):
                el_mode = "DEFAULT" if mode == "FIELD" else "VALUE"
            elif mode in ("OUT", "DEFAULT"):
                el_mode = "DEFAULT"
            else:
                el_mode = "VALUE"
            if t.is_array and t.name == "byte":
                name = "u8"
            else:
                name = self.base_name(el, el_mode, scope)
            auto = self.auto_constructor(el, scope)
            if (el_mode == "DEFAULT" and not auto) or (
                    t.nullable and not self.primitive_or_enum(el, scope)):
                name = f"Option<{name}>"
            if mode == "UNSIZED":
                name = f"[{name}]"
            elif t.is_array and all(x is not None for x in t.dims):
                for dim in reversed(t.dims):
                    name = f"[{name}; {dim}]"
            else:
                name = f"alloc::vec::Vec<{name}>"
        else:
            name = self.base_name(t, mode, scope)
        if mode in ("IN", "UNSIZED"):
            name = "&" + name
        if t.nullable or (self.needs_option(t, scope) and mode in ("DEFAULT", "OUT", "FIELD")):
            name = f"Option<alloc::boxed::Box<{name}>>" if t.heap else f"Option<{name}>"
        if mode in ("OUT", "INOUT"):
            name = "&mut " + name
        return name

    def base_name(self, t, mode, scope):
        if t.name in PRIMITIVES:
            return PRIMITIVES[t.name]
        if t.name == "void":
            return "()"
        if t.name == "String":
            return "str" if mode == "UNSIZED" else BUILTINS["String"]
        if t.name in BUILTINS:
            return BUILTINS[t.name]
        if t.name == "ParcelableHolder":
            return "binder::ParcelableHolder<binder::binder_impl::LocalStabilityType>"
        d = self.w.resolve(t.name, scope)
        p = self.path(d)
        return f"binder::Strong<dyn {p}>" if d.kind == "interface" else p

    def primitive_or_enum(self, t, scope):
        if t.name in PRIMITIVES:
            return True
        d = self.w.resolve(t.name, scope)
        return d is not None and d.kind == "enum"

    def auto_constructor(self, t, scope):
        if t.name in ("ParcelFileDescriptor", "IBinder"):
            return False
        d = self.w.resolve(t.name, scope)
        return not (d is not None and d.kind == "interface")

    def needs_option(self, t, scope):
        if t.is_array or t.is_list or t.nullable:
            return False
        if t.name in ("IBinder", "ParcelFileDescriptor"):
            return True
        d = self.w.resolve(t.name, scope)
        return d is not None and d.kind == "interface"

    def arg_mode(self, direction, t, scope):
        if direction != "in":
            return "INOUT" if direction == "inout" else "OUT"
        if t.name == "String" or any(x is None for x in t.dims) or t.is_list:
            return "UNSIZED"
        if not self.primitive_or_enum(t, scope) or (t.is_array and all(x is not None for x in t.dims)):
            return "IN"
        return "VALUE"

    # ---- literals
    def literal(self, ty, value):
        if ty.name == "String":
            return '"' + str(value).replace("\\", "\\\\").replace('"', '\\"') + '"'
        if isinstance(value, bool):
            return "true" if value else "false"
        if ty.name in ("float", "double"):
            return repr(float(value))
        return str(int(value))

    def const_decl(self, d):
        out = []
        for ty, name, expr in d.consts:
            v = self.w.evaluate(expr, d)
            rt = "&'static str" if ty.name == "String" else self.rust_type(ty, "VALUE", d)
            out.append((rid(name), rt, self.literal(ty, v)))
        return out

    def default_value(self, ty, expr, d):
        if expr is None:
            return "Default::default()"
        if ty.is_array or ty.is_list or ty.nullable:
            return "Default::default()"
        if ty.name in PRIMITIVES or ty.name == "String":
            return self.literal(ty, self.w.evaluate(expr, d)) + (
                ".to_string()" if ty.name == "String" else "")
        decl = self.w.resolve(ty.name, d)
        if decl is not None and decl.kind == "enum":
            try:
                return f"{self.path(decl)}({self.w.evaluate(expr, d)})"
            except SystemExit:
                return "Default::default()"
        return "Default::default()"

    # ---- one type -> the body of `pub mod Name`
    def body(self, d):
        o = []
        if d.kind == "parcelable" and not d.structured:
            return ""
        derives = ["Debug"] + [x for x in d.derives if x != "Debug"]
        n = rid(d.name)
        if d.kind == "parcelable":
            o.append(f"#[derive({', '.join(derives)})]")
            o.append(f"pub struct {n} {{")
            for ty, name, _ in d.fields:
                o.append(f"  pub {rid(name)}: {self.rust_type(ty, 'FIELD', d)},")
            o.append("}")
            consts = self.const_decl(d)
            if consts:
                o.append(f"impl {n} {{")
                o += [f"  pub const {c}: {t} = {v};" for c, t, v in consts]
                o.append("}")
            o.append(f"impl Default for {n} {{")
            o.append("  fn default() -> Self {")
            o.append("    Self {")
            for ty, name, expr in d.fields:
                o.append(f"      {rid(name)}: {self.default_value(ty, expr, d)},")
            o.append("    }")
            o.append("  }")
            o.append("}")
        elif d.kind == "union":
            o.append(f"#[derive({', '.join(derives)})]")
            o.append(f"pub enum {n} {{")
            first = None
            for ty, name, _ in d.fields:
                cap = name[0].upper() + name[1:]
                first = first or (cap, ty)
                o.append(f"  {rid(cap)}({self.rust_type(ty, 'FIELD', d)}),")
            o.append("}")
            o.append(f"impl Default for {n} {{")
            o.append(f"  fn default() -> Self {{ Self::{rid(first[0])}(Default::default()) }}")
            o.append("}")
        elif d.kind == "enum":
            back = BACKING[d.backing]
            o.append("use binder::declare_binder_enum;")
            o.append("declare_binder_enum! {")
            o.append(f"  {n} : [{back}; {len(d.enumerators)}] {{")
            for name, _ in d.enumerators:
                o.append(f"    {rid(name)} = {self.w.enum_value(d, name)},")
            o.append("  }")
            o.append("}")
        else:
            o += self.interface_body(d)
        return "\n".join(o)

    def interface_body(self, d):
        n, o = rid(d.name), []
        for c, t, v in self.const_decl(d):
            o.append(f"pub const {c}: {t} = {v};")
        o.append(f"pub trait {n}: binder::Interface + Send {{")
        o.append(f"  fn get_descriptor() -> &'static str where Self: Sized {{ \"{d.full}\" }}")
        sigs = []
        for ret, name, args, _ in d.methods:
            params = "".join(
                f", _arg_{a}: {self.rust_type(t, self.arg_mode(dr, t, d), d)}" for dr, t, a in args)
            rt = self.rust_type(ret, "VALUE", d)
            sig = f"{rid(name)}(&self{params}) -> binder::Result<{rt}>"
            sigs.append(sig)
            o.append(f"  fn {sig};")
        o.append("  fn r#getInterfaceVersion(&self) -> binder::Result<i32> { Ok(0) }")
        o.append("  fn r#getInterfaceHash(&self) -> binder::Result<alloc::string::String> "
                 "{ Ok(alloc::string::String::new()) }")
        o.append("}")
        # The binder macro implements Debug for the trait object; parcelables with interface
        # fields derive Debug through it.
        o.append(f"impl core::fmt::Debug for dyn {n} + '_ {{ "
                 f"fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result "
                 f"{{ f.pad(\"{n}\") }} }}")
        o.append(f"pub struct {rid('Bn' + d.name)}(());")
        o.append(f"impl {rid('Bn' + d.name)} {{")
        o.append(f"  pub fn new_binder<T: {n} + Send + Sync + 'static>(_inner: T, "
                 f"_features: binder::BinderFeatures) -> binder::Strong<dyn {n}> {{ "
                 f"unimplemented!(\"stand-in\") }}")
        o.append("}")
        bp = rid("Bp" + d.name)
        o.append(f"pub struct {bp} {{ _binder: binder::SpIBinder }}")
        o.append(f"impl {bp} {{")
        o.append(f"  pub fn new(_binder: binder::SpIBinder) -> Option<binder::Strong<dyn {n}>> "
                 f"{{ unimplemented!(\"stand-in\") }}")
        o.append("}")
        o.append(f"impl binder::Interface for {bp} {{}}")
        o.append(f"impl {n} for {bp} {{")
        for sig in sigs:
            o.append(f"  fn {sig} {{ unimplemented!(\"stand-in\") }}")
        o.append("}")
        o.append(f"impl binder::FromIBinder for dyn {n} {{")
        o.append(f"  fn try_from(_ibinder: binder::SpIBinder) -> binder::Result<binder::Strong<dyn {n}>> "
                 f"{{ unimplemented!(\"stand-in\") }}")
        o.append("}")
        return o

    def module(self, d):
        inner = self.body(d)
        for nd in d.nested:
            inner += f"\npub mod {rid(nd.name)} {{\n{self.module_inner(nd)}\n}}"
        return f"pub mod {rid(d.name)} {{\n{inner}\n}}"

    def module_inner(self, d):
        inner = self.body(d)
        for nd in d.nested:
            inner += f"\npub mod {rid(nd.name)} {{\n{self.module_inner(nd)}\n}}"
        return inner


def tree_emit(tree, depth=0):
    out = []
    for key in sorted(tree):
        if key == "__mods__":
            continue
        out.append(f"pub mod {rid(key)} {{")
        out.append(tree_emit(tree[key], depth + 1))
        out.append("}")
    out += tree.get("__mods__", [])
    return "\n".join(out)


def generate(world, crate, decls, modules):
    em = Emitter(world, crate)
    tree = {}
    for d in sorted(decls, key=lambda x: x.full):
        node = tree
        for part in d.pkg.split("."):
            node = node.setdefault(part, {})
        node.setdefault("__mods__", []).append(em.module(d))
    body = tree_emit({"aidl": tree})
    lib = (
        f"// Generated by fvs-harness/tools/aidl_stub_gen.py from: {', '.join(modules)}.\n"
        "// Stand-in for the Soong-generated Rust crate: same item paths and signatures, bodies panic.\n"
        "// Do not edit; change the generator and regenerate.\n"
        "#![allow(non_snake_case, non_camel_case_types, non_upper_case_globals, unused_imports,\n"
        "         unused_variables, dead_code, clippy::all)]\n"
        "extern crate alloc;\n"
        "pub use binder;\n" + body + "\n")
    deps = sorted(em.deps)
    toml = (
        "# Generated by fvs-harness/tools/aidl_stub_gen.py. Do not edit.\n"
        "[package]\n"
        f'name = "{crate}"\nversion = "0.0.0"\nedition = "2021"\npublish = false\n\n'
        '[lib]\npath = "src/lib.rs"\n\n'
        "[dependencies]\n"
        'binder = { path = "../../binder" }\n'
        + "".join(f'{d} = {{ path = "../{d}" }}\n' for d in deps))
    return {"Cargo.toml": toml, "src/lib.rs": lib}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--out", default=str(HARNESS / "aidl"))
    args = ap.parse_args()
    world, by_crate = World(), {}
    for crate, dirs in CRATES.items():
        for dd in dirs:
            for f in sorted(pathlib.Path(dd).rglob("*.aidl")):
                for d in Parser(lex(f.read_text()), crate, f).unit():
                    world.add(d)
                    by_crate.setdefault(crate, []).append(d)
    produced = {}
    for crate, decls in by_crate.items():
        names = [str(pathlib.Path(x).relative_to(REPO)) for x in CRATES[crate]]
        for rel, text in generate(world, crate, decls, names).items():
            produced[pathlib.Path(args.out) / crate / rel] = text
    if args.check:
        bad = [str(p) for p, t in produced.items() if not p.exists() or p.read_text() != t]
        stale = [str(p) for p in pathlib.Path(args.out).rglob("*") if p.is_file() and p not in produced]
        for b in bad:
            print(f"differs: {b}", file=sys.stderr)
        for s in stale:
            print(f"not generated: {s}", file=sys.stderr)
        sys.exit(1 if bad or stale else 0)
    for p, t in produced.items():
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(t)
    print(f"wrote {len(produced)} files for {len(by_crate)} crates under {args.out}", file=sys.stderr)


if __name__ == "__main__":
    main()
