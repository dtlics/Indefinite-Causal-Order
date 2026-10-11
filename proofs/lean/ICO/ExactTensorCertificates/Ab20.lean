import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ab_20_20 : abIdentity 20 20 := by unfold abIdentity; decide +kernel
theorem ab_20_21 : abIdentity 20 21 := by unfold abIdentity; decide +kernel
theorem ab_20_22 : abIdentity 20 22 := by unfold abIdentity; decide +kernel
theorem ab_20_23 : abIdentity 20 23 := by unfold abIdentity; decide +kernel
theorem ab_20_24 : abIdentity 20 24 := by unfold abIdentity; decide +kernel

end ICO.ExactTensorCertificates
