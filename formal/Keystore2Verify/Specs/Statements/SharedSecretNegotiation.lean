import Keystore2Verify.Proofs.SharedSecretNegotiation.SharedSecretParticipant

namespace Keystore2Verify.SharedSecretNegotiation

section SharedSecretParticipant
open Aeneas Aeneas.Std Result keystore2
open shared_secret_negotiation
open Keystore2Verify.LegacyImporter
open SharedSecretParticipant.Insts

recall participant_clone_aidl (s s' : String)
    (h : alloc.string.String.Insts.CoreCloneClone.clone s = ok s') :
    CoreCloneClone.clone (SharedSecretParticipant.Aidl s) =
      ok (SharedSecretParticipant.Aidl s')

recall participant_clone_hidl (b : Bool) (p : Std.Usize × Std.Usize) :
    CoreCloneClone.clone (SharedSecretParticipant.Hidl b p) =
      ok (SharedSecretParticipant.Hidl b p)

recall participant_eq_variants_differ (s : String) (b : Bool) (p : Std.Usize × Std.Usize) :
    CoreCmpPartialEqSharedSecretParticipant.eq (.Aidl s) (.Hidl b p) = ok false ∧
    CoreCmpPartialEqSharedSecretParticipant.eq (.Hidl b p) (.Aidl s) = ok false

recall participant_eq_aidl (s t : String) :
    CoreCmpPartialEqSharedSecretParticipant.eq (.Aidl s) (.Aidl t) =
      alloc.string.String.Insts.CoreCmpPartialEqString.eq s t

recall participant_eq_hidl_flag (b c : Bool) (p q : Std.Usize × Std.Usize) (h : b ≠ c) :
    CoreCmpPartialEqSharedSecretParticipant.eq (.Hidl b p) (.Hidl c q) = ok false

recall participant_eq_hidl_pair (b : Bool) (p q : Std.Usize × Std.Usize) :
    CoreCmpPartialEqSharedSecretParticipant.eq (.Hidl b p) (.Hidl b q) =
      Pair.Insts.CoreCmpPartialEqPair.eq core.cmp.PartialEqUsize core.cmp.PartialEqUsize p q

recall participant_cmp_variants_differ (s : String) (b : Bool) (p : Std.Usize × Std.Usize) :
    CoreCmpOrd.cmp (.Aidl s) (.Hidl b p) = ok Ordering.lt ∧
    CoreCmpOrd.cmp (.Hidl b p) (.Aidl s) = ok Ordering.gt

recall participant_cmp_aidl (s t : String) :
    CoreCmpOrd.cmp (.Aidl s) (.Aidl t) = alloc.string.String.Insts.CoreCmpOrd.cmp s t

recall participant_cmp_hidl_flag (b c : Bool) (p q : Std.Usize × Std.Usize) (o : Ordering)
    (h : Bool.Insts.CoreCmpOrd.cmp b c = ok o) (ho : o ≠ Ordering.eq) :
    CoreCmpOrd.cmp (.Hidl b p) (.Hidl c q) = ok o

recall participant_cmp_hidl_pair (b c : Bool) (p q : Std.Usize × Std.Usize)
    (h : Bool.Insts.CoreCmpOrd.cmp b c = ok Ordering.eq) :
    CoreCmpOrd.cmp (.Hidl b p) (.Hidl c q) =
      Pair.Insts.CoreCmpOrd.cmp core.cmp.OrdUsize core.cmp.OrdUsize p q

recall participant_partial_cmp (x y : SharedSecretParticipant) (o : Ordering)
    (h : CoreCmpOrd.cmp x y = ok o) :
    CoreCmpPartialOrdSharedSecretParticipant.partial_cmp x y = ok (some o)

recall participant_clone_eq (hs : StringCloneSpec) (x : SharedSecretParticipant) :
    CoreCloneClone.clone x = ok x

recall participant_eq_iff (hs : StringEqSpec) (hp : PairEqSpec) (x y : SharedSecretParticipant) :
    ∃ b, CoreCmpPartialEqSharedSecretParticipant.eq x y = ok b ∧ (b = true ↔ x = y)

recall participant_cmp_lex (hs : StringCmpSpec) (hb : BoolCmpSpec) (hp : PairCmpSpec)
    (x y : SharedSecretParticipant) :
    CoreCmpOrd.cmp x y = ok (participantOrd x y)

recall participant_partial_cmp_lex (hs : StringCmpSpec) (hb : BoolCmpSpec) (hp : PairCmpSpec)
    (x y : SharedSecretParticipant) :
    CoreCmpPartialOrdSharedSecretParticipant.partial_cmp x y = ok (some (participantOrd x y))

end SharedSecretParticipant

end Keystore2Verify.SharedSecretNegotiation
