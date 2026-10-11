import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem gauge_24_24 : gaugeIdentity 24 24 := by unfold gaugeIdentity; decide +kernel

end ICO.ExactTensorCertificates
