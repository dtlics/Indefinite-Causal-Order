import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem gauge_20_20 : gaugeIdentity 20 20 := by unfold gaugeIdentity; decide +kernel
theorem gauge_20_21 : gaugeIdentity 20 21 := by unfold gaugeIdentity; decide +kernel
theorem gauge_20_22 : gaugeIdentity 20 22 := by unfold gaugeIdentity; decide +kernel
theorem gauge_20_23 : gaugeIdentity 20 23 := by unfold gaugeIdentity; decide +kernel
theorem gauge_20_24 : gaugeIdentity 20 24 := by unfold gaugeIdentity; decide +kernel

end ICO.ExactTensorCertificates
