import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem gauge_21_21 : gaugeIdentity 21 21 := by unfold gaugeIdentity; decide +kernel
theorem gauge_21_22 : gaugeIdentity 21 22 := by unfold gaugeIdentity; decide +kernel
theorem gauge_21_23 : gaugeIdentity 21 23 := by unfold gaugeIdentity; decide +kernel
theorem gauge_21_24 : gaugeIdentity 21 24 := by unfold gaugeIdentity; decide +kernel

end ICO.ExactTensorCertificates
