import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem gauge_23_23 : gaugeIdentity 23 23 := by unfold gaugeIdentity; decide +kernel
theorem gauge_23_24 : gaugeIdentity 23 24 := by unfold gaugeIdentity; decide +kernel

end ICO.ExactTensorCertificates
