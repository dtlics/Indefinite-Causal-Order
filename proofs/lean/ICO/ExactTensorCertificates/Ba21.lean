import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ba_21_21 : baIdentity 21 21 := by unfold baIdentity; decide +kernel
theorem ba_21_22 : baIdentity 21 22 := by unfold baIdentity; decide +kernel
theorem ba_21_23 : baIdentity 21 23 := by unfold baIdentity; decide +kernel
theorem ba_21_24 : baIdentity 21 24 := by unfold baIdentity; decide +kernel

end ICO.ExactTensorCertificates
