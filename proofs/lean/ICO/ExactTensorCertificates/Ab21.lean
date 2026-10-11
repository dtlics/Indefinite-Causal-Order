import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ab_21_21 : abIdentity 21 21 := by unfold abIdentity; decide +kernel
theorem ab_21_22 : abIdentity 21 22 := by unfold abIdentity; decide +kernel
theorem ab_21_23 : abIdentity 21 23 := by unfold abIdentity; decide +kernel
theorem ab_21_24 : abIdentity 21 24 := by unfold abIdentity; decide +kernel

end ICO.ExactTensorCertificates
