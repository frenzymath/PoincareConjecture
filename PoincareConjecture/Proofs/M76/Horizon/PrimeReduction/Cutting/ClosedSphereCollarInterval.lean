import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.ClosedCollarIntervalGeometry
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphereCutPLDomain









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

theorem ChartwisePLSphere.closed_bicollar_interval_domain
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (F : X → E) (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F S) {N : Set E} (hN : N = F '' S) (hNc : IsCompact N)
    (c : E × ℝ → X) (hc : PolyhedralPLInCharts e c (N ×ˢ I))
    (hci : Topology.IsEmbedding (fun z : (N ×ˢ I : Set (E × ℝ)) => c z))
    {a b : ℝ} (ha : -1 < a) (hab : a < b) (hb : b < 1)
    (hopen : IsOpen (c '' (N ×ˢ Ioo a b))) :
    let K := c '' (N ×ˢ Icc a b)
    let B : Bool → Set X := fun side => c '' (N ×ˢ {if side then b else a})
    IsCompact K ∧ PLDomain e K ∧ interior K = c '' (N ×ˢ Ioo a b) ∧
      (∀ side, Nonempty (ChartwisePLSphere e (B side))) ∧
      Disjoint (B false) (B true) ∧ frontier K = B false ∪ B true := by
  let K := c '' (N ×ˢ Icc a b)
  let B : Bool → Set X := fun side => c '' (N ×ˢ {if side then b else a})
  have hinj : InjOn c (N ×ˢ I) := by
    intro z hz w hw hzw
    exact congrArg Subtype.val (hci.injective (a₁ := ⟨z,hz⟩) (a₂ := ⟨w,hw⟩) hzw)
  obtain ⟨hK,hKi,hreg,hfront⟩ := closed_collar_interval_geometry hNc c hc.continuousOn
    hinj ha hab hb hopen
  have hB (side : Bool) : Nonempty (ChartwisePLSphere e (B side)) := by
    obtain ⟨sB,_⟩ := s.exists_bicollar_level_sphere F hF hFi hN c hc hci
      (show (if side then b else a) ∈ I by
        cases side <;> simp only [Bool.false_eq_true,reduceIte] <;> constructor <;> linarith)
    exact ⟨sB⟩
  have hdis : Disjoint (B false) (B true) := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,hzx⟩ ⟨w,hw,hwx⟩
    have hza : z.2 = a := hz.2
    have hwb : w.2 = b := hw.2
    have heq := congrArg Prod.snd (hinj
      ⟨hz.1,by rw [hza]; exact ⟨ha.le,hab.le.trans hb.le⟩⟩
      ⟨hw.1,by rw [hwb]; exact ⟨ha.le.trans hab.le,hb.le⟩⟩
      (hzx.trans hwx.symm))
    linarith
  have hfront' : frontier K = B false ∪ B true := hfront
  refine ⟨hK,?_,hKi,hB,hdis,hfront'⟩
  obtain ⟨s0⟩ := hB false
  obtain ⟨s1⟩ := hB true
  refine ⟨hcover,hcompat,hK.isClosed,?_⟩
  intro x hx
  rcases hfront'.subset hx with hx0 | hx1
  · exact s0.exists_regular_boundary_halfspace_chart hK.isClosed hreg s1.isCompact.isClosed
      hcompat hcover (hfront'.trans (union_comm _ _)) hx0
      (fun hx1 => disjoint_left.mp hdis hx0 hx1)
  · exact s1.exists_regular_boundary_halfspace_chart hK.isClosed hreg s0.isCompact.isClosed
      hcompat hcover hfront' hx1 (fun hx0 => disjoint_left.mp hdis hx0 hx1)

theorem isOpen_bicollar_subinterval
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {N : Set E} {c : E × ℝ → X}
    (hci : Topology.IsEmbedding (fun z : (N ×ˢ I : Set (E × ℝ)) => c z))
    {a b ε : ℝ} (hεsmall : ε ≤ 1)
    (hsub : Ioo a b ⊆ Ioo (-ε) ε)
    (hopen : IsOpen (c '' (N ×ˢ Ioo (-ε) ε))) :
    IsOpen (c '' (N ×ˢ Ioo a b)) := by
  let V : Set (N ×ˢ I : Set (E × ℝ)) := {z | z.1.2 ∈ Ioo a b}
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val)
  have hVe : (fun z : (N ×ˢ I : Set (E × ℝ)) => c z) '' V = c '' (N ×ˢ Ioo a b) := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨z,⟨z.property.1,hz⟩,rfl⟩
    · rintro _ ⟨z,hz,rfl⟩
      have ht := hsub hz.2
      exact ⟨⟨z,hz.1,by linarith [ht.1],by linarith [ht.2]⟩,hz.2,rfl⟩
  rw [←hVe]
  apply hci.isInducing.isOpen_image_of_subset_open hV hopen
  · rintro _ ⟨z,hz,rfl⟩
    exact ⟨z,⟨z.property.1,hsub hz⟩,rfl⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact ⟨⟨z,hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩,rfl⟩

end PoincareConjecture.M76
