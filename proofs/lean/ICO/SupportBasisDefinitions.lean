import ICO.SupportModularTree
namespace ICO.SupportModularTree
open ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def basisProductRe (r b : Nat) : Int :=
  sumBelow 128 (fun k => (gaussianEntry r k).1 * basisEntry k b)
def basisProductIm (r b : Nat) : Int :=
  sumBelow 128 (fun k => (gaussianEntry r k).2 * basisEntry k b)
end ICO.SupportModularTree
