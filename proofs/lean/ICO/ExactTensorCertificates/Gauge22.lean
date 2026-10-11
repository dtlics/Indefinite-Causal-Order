import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem gauge_22_22 : gaugeIdentity 22 22 := by unfold gaugeIdentity; decide +kernel
theorem gauge_22_23 : gaugeIdentity 22 23 := by unfold gaugeIdentity; decide +kernel
theorem gauge_22_24 : gaugeIdentity 22 24 := by unfold gaugeIdentity; decide +kernel

end ICO.ExactTensorCertificates
