import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ab_24_24 : abIdentity 24 24 := by unfold abIdentity; decide +kernel

end ICO.ExactTensorCertificates
