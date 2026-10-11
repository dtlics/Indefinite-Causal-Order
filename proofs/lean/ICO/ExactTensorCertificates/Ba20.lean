import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ba_20_20 : baIdentity 20 20 := by unfold baIdentity; decide +kernel
theorem ba_20_21 : baIdentity 20 21 := by unfold baIdentity; decide +kernel
theorem ba_20_22 : baIdentity 20 22 := by unfold baIdentity; decide +kernel
theorem ba_20_23 : baIdentity 20 23 := by unfold baIdentity; decide +kernel
theorem ba_20_24 : baIdentity 20 24 := by unfold baIdentity; decide +kernel

end ICO.ExactTensorCertificates
