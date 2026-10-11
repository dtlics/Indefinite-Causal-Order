import ICO.ProtocolSchedule
import ICO.RecordingDepolarizing

namespace ICO.SequentialIsometry
open Matrix QIT ICO.ClassicalDilation
open scoped BigOperators
noncomputable section
universe u
set_option maxHeartbeats 1200000
variable {A B O E M : Type u} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
  [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M]

theorem erasedKraus_gram (W : Matrix (O×E) B ℂ) :
    (∑ e,(erasedKraus W e).conjTranspose*erasedKraus W e)=W.conjTranspose*W := by
  ext a b
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    erasedKraus,Fintype.sum_prod_type]
  exact Finset.sum_comm

def erasureChannel (W : Matrix (O×E) B ℂ) (hW : W.conjTranspose*W=1) : Channel B O where
  map := MatrixMap.ofKraus (erasedKraus W)
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa only [MatrixMap.krausAdjoint,Matrix.mul_one,erasedKraus_gram] using hW)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

theorem erasureChannel_TNI (W : Matrix (O×E) B ℂ) (hW : W.conjTranspose*W=1) :
    MatrixMap.TraceNonincreasingCP (erasureChannel W hW).map :=
  MatrixMap.traceNonincreasingCP_of_tracePreserving
    (erasureChannel W hW).completelyPositive (erasureChannel W hW).tracePreserving

def Protocol.terminalChannel {q : ℕ} (p : Protocol A (A×M) O q) :
    Channel (A×p.tailMemory (q+1)) O := erasureChannel p.tailFinal p.tailFinal_isometry

variable [Nonempty A]

def depolarizingKraus : (A×A) → CMatrix A :=
  channelKraus (ICO.RecordingDepolarizing.depolarizing (α:=A))

theorem depolarizingKraus_complete :
    (∑ i,(depolarizingKraus (A:=A) i).conjTranspose*depolarizingKraus i)=1 := by
  have h := MatrixMap.krausAdjoint_one_of_tracePreserving
    (channelKraus (ICO.RecordingDepolarizing.depolarizing (α:=A)))
    (by rw [←channelKraus_map]; exact ICO.RecordingDepolarizing.depolarizing.tracePreserving)
  simpa only [MatrixMap.krausAdjoint,Matrix.mul_one,depolarizingKraus] using h

theorem depolarizingKraus_memory :
    ICO.AllChannelDilation.oracleMap (M:=M) (depolarizingKraus (A:=A)) =
      (ICO.RecordingDepolarizing.withMemory (α:=A) (μ:=M)).map := by
  rw [ICO.OracleLift.oracleMap_lift]
  ext X x y
  change MatrixMap.ofKraus (channelKraus ICO.RecordingDepolarizing.depolarizing)
    (fun a b => X (a,x.2) (b,y.2)) x.1 y.1 =
    MatrixMap.kron ICO.RecordingDepolarizing.depolarizing.map (Channel.idChannel M).map X x y
  rw [MatrixMap.kron_idChannel_apply_slice,←channelKraus_map]

#print axioms erasureChannel_TNI
#print axioms depolarizingKraus_memory
#print axioms depolarizingKraus_complete
end
end ICO.SequentialIsometry
