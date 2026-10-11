import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ab_23_23 : abIdentity 23 23 := by unfold abIdentity; decide +kernel
theorem ab_23_24 : abIdentity 23 24 := by unfold abIdentity; decide +kernel

end ICO.ExactTensorCertificates
