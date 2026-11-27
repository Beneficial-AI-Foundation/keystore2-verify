import Keystore2Verify.Specs.Defs.Database

namespace Keystore2Verify.Database
open Aeneas Aeneas.Std Result keystore2
open Keystore2Verify.Externals
open database.CertificateInfo.Insts.CoreDefaultDefault renaming default → certInfoDefault
open database.CertificateInfo renaming take_cert → certInfoTakeCert
open database.CertificateInfo renaming take_cert_chain → certInfoTakeCertChain
open database.BlobInfo renaming new_with_superseded → blobInfoNewWithSuperseded

/-- conditional: `default` never fails and returns the value without certificate and without
certificate chain. Hypothesis: `OptionDefaultSpec` for the certificate. -/
theorem certificate_info_default (h : OptionDefaultSpec (alloc.vec.Vec Std.U8)) :
    certInfoDefault = ok { cert := none, cert_chain := none } := by
  sorry

/-- exact: `take_cert` never fails. It returns the certificate and leaves `None` in its place.
The certificate chain does not change. -/
theorem certificate_info_take_cert (c : database.CertificateInfo) :
    certInfoTakeCert c = ok (c.cert, { c with cert := none }) := by
  sorry

/-- exact: `take_cert_chain` never fails. It returns the certificate chain and leaves `None` in
its place. The certificate does not change. -/
theorem certificate_info_take_cert_chain (c : database.CertificateInfo) :
    certInfoTakeCertChain c = ok (c.cert_chain, { c with cert_chain := none }) := by
  sorry

/-- exact: `BlobInfo::new_with_superseded` never fails and stores its three arguments as the
blob, its metadata and the superseded blob. -/
theorem blob_info_new_with_superseded (blob : Slice Std.U8) (md : database.BlobMetaData)
    (sup : Option (Slice Std.U8 × database.BlobMetaData)) :
    blobInfoNewWithSuperseded blob md sup =
      ok { blob := blob, metadata := md, superseded_blob := sup } := by
  sorry
