import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ab_22_22 : abIdentity 22 22 := by unfold abIdentity; decide +kernel
theorem ab_22_23 : abIdentity 22 23 := by unfold abIdentity; decide +kernel
theorem ab_22_24 : abIdentity 22 24 := by unfold abIdentity; decide +kernel

end ICO.ExactTensorCertificates
