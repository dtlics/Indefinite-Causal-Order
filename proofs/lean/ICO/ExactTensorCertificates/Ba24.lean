import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ba_24_24 : baIdentity 24 24 := by unfold baIdentity; decide +kernel

end ICO.ExactTensorCertificates
