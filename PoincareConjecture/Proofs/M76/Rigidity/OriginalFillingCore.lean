import PoincareConjecture.Proofs.M76.Rigidity.OriginalCollarCore
import PoincareConjecture.Proofs.M76.Rigidity.OriginalFillingOuterCollar
import PoincareConjecture.Proofs.M76.Rigidity.OriginalFillingCoreEquality
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PositiveCollarOpen









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}





theorem ball_eq_collar_core (P : OriginalDiskProduct e R j)
    (hK : IsCompact P.cutCarrier)
    (hfront : frontier P.cutCarrier = (frontier R \ P.openStrip) ∪ P.endDisks)
    (sph : ChartwisePLSphere e (frontier P.cutCarrier))
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (HB : L.space ≃ₜ frontier P.cutCarrier) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ I))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z))
    (hinside : MapsTo c (L.space ×ˢ I) P.cutCarrier)
    (hbase : ∀ z : L.space, c ((z : E), 0) = HB z)
    (hproper : ∀ z : (L.space ×ˢ I : Set (E × ℝ)),
      c z ∈ frontier P.cutCarrier ↔ (z : E × ℝ).2 = 0)
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 2)
    (hopen : ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      IsOpen ((Subtype.val : P.cutCarrier → X) ⁻¹' (c '' (L.space ×ˢ Ico 0 ε))))
    {Db : Set X} (b : ChartwisePLBall e Db (c '' (L.space ×ˢ {δ / 2})))
    (hDbR : Db ⊆ R) (hlevelInt : c '' (L.space ×ˢ {δ / 2}) ⊆ interior P.cutCarrier) :
    Db = P.cutCarrier \ (c '' (L.space ×ˢ Ico 0 (δ / 2))) ∧
      Nonempty (ChartwisePLBall e (P.cutCarrier \ (c '' (L.space ×ˢ Ico 0 (δ / 2))))
        (c '' (L.space ×ˢ {δ / 2}))) := by
  obtain ⟨_, hC, _⟩ := sph.collar_core hK L hL HB c hc hi hinside hbase hproper
    hδ hδsmall hopen
  have hBC := P.ball_subset_collar_core hfront sph L hL HB c hc hi hinside hbase
    (half_pos hδ) (by linarith) b hDbR hlevelInt
  have hLconn : IsConnected L.space := isConnected_iff_connectedSpace.mpr
    (HB.connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp sph.isConnected))
  have hinj : InjOn c (L.space ×ˢ I) := by
    intro z hz w hw heq
    have h : (⟨z, hz⟩ : (L.space ×ˢ I : Set (E × ℝ))) = ⟨w, hw⟩ := hi.injective heq
    exact congrArg Subtype.val h
  have hopenPositive := (isOpen_positive_collar c hinside hproper (by linarith : δ ≤ 1)
    (hopen δ hδ le_rfl)).1
  have heq := b.eq_core_of_positive_collar c hLconn hc.continuousOn hinj
    (half_pos hδ) (by linarith : δ / 2 < δ) (by linarith : δ ≤ 1) hopenPositive hBC hC
  exact ⟨heq, ⟨heq ▸ b⟩⟩

end PoincareConjecture.M76.OriginalDiskProduct
