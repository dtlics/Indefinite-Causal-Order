import ICO.ExactTensorDefinitions

namespace ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ba_23_23 : baIdentity 23 23 := by unfold baIdentity; decide +kernel
theorem ba_23_24 : baIdentity 23 24 := by unfold baIdentity; decide +kernel

end ICO.ExactTensorCertificates
