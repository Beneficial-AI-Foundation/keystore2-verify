// RECONSTRUCTED by hand for the fvs-harness stand-in; this is not the AOSP file.
// The AOSP source of the Soong module packagemanager_aidl was not located at the tag
// android-17.0.0_r1 (it is not in frameworks/base core/java/android/content/pm or in
// frameworks/native). This file declares only what keystore2/src/utils.rs calls
// (getPackageInfoWithSigningInfoForUid, getTargetSdkVersionForPackage, getLocationFlags,
// LOCATION_SYSTEM). Types and values come from those call sites, not from the real interface.
package android.content.pm;

interface IPackageManagerNative {
    const int LOCATION_SYSTEM = 0x1;
    const int LOCATION_VENDOR = 0x2;
    const int LOCATION_PRODUCT = 0x4;

    @nullable PackageInfo[] getPackageInfoWithSigningInfoForUid(int uid);
    int getTargetSdkVersionForPackage(String packageName);
    int getLocationFlags(String packageName);
}
