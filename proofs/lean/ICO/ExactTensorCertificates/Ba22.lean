import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ba_22_22 : baIdentity 22 22 := by unfold baIdentity; decide +kernel
theorem ba_22_23 : baIdentity 22 23 := by unfold baIdentity; decide +kernel
theorem ba_22_24 : baIdentity 22 24 := by unfold baIdentity; decide +kernel

end ICO.ExactTensorCertificates
