import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Partition.GraphRegions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

def closedGraphSlab (f k : UnitTwoSphere → ℝ) : Set M :=
  {x | x ∈ N.carrier ∧ f (N.coordinate_inverse x).1 ≤ (N.coordinate_inverse x).2 ∧
    (N.coordinate_inverse x).2 ≤ k (N.coordinate_inverse x).1}

theorem mem_closedGraphSlab_coordinate_map_iff (f k : UnitTwoSphere → ℝ)
    {q : UnitTwoSphere} {t : ℝ} (ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    N.coordinate_map (q, t) ∈ N.closedGraphSlab f k ↔ f q ≤ t ∧ t ≤ k q := by
  have hz : (q, t) ∈ N.cylinderDomain := ⟨mem_univ _, ht⟩
  simp only [closedGraphSlab, mem_ofPred_eq, N.coordinate_map_mem hz, true_and,
    N.coordinate_inverse_coordinate_map hz]

theorem isCompact_closedGraphSlab (f k : UnitTwoSphere → ℝ)
    (hf : Continuous f) (hk : Continuous k)
    (hfdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hkdom : ∀ q, k q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hfk : ∀ q, f q < k q) : IsCompact (N.closedGraphSlab f k) := by
  let F : RoundCylinderSpace → RoundCylinderSpace :=
    fun p => (p.1, (1 - p.2) * f p.1 + p.2 * k p.1)
  have hF : Continuous F := continuous_fst.prodMk
    (((continuous_const.sub continuous_snd).mul (hf.comp continuous_fst)).add
      (continuous_snd.mul (hk.comp continuous_fst)))
  have hbounds (p : RoundCylinderSpace) (hp : p ∈ univ ×ˢ Icc (0 : ℝ) 1) :
      f p.1 ≤ (F p).2 ∧ (F p).2 ≤ k p.1 := by
    dsimp [F]
    have h0 := mul_nonneg hp.2.1 (sub_nonneg.mpr (hfk p.1).le)
    have h1 := mul_nonneg (sub_nonneg.mpr hp.2.2) (sub_nonneg.mpr (hfk p.1).le)
    constructor <;> nlinarith
  have hmem : MapsTo F (univ ×ˢ Icc (0 : ℝ) 1) N.cylinderDomain := by
    intro p hp
    exact ⟨mem_univ _, (hfdom p.1).1.trans_le (hbounds p hp).1,
      (hbounds p hp).2.trans_lt (hkdom p.1).2⟩
  have hEq : (N.coordinate_map ∘ F) '' (univ ×ˢ Icc (0 : ℝ) 1) =
      N.closedGraphSlab f k := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨N.coordinate_map_mem (hmem hp), ?_⟩
      dsimp only [Function.comp_apply]
      rw [N.coordinate_inverse_coordinate_map (hmem hp)]
      exact hbounds p hp
    · rintro ⟨hx, hlo, hhi⟩
      let q := (N.coordinate_inverse x).1
      let a := (N.coordinate_inverse x).2
      let t := (a - f q) / (k q - f q)
      have hgap : 0 < k q - f q := sub_pos.mpr (hfk q)
      have ht : t ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (sub_nonneg.mpr hlo) hgap.le,
          (div_le_one hgap).mpr (by dsimp [q, a]; linarith)⟩
      have hcoord : F (q, t) = N.coordinate_inverse x := by
        apply Prod.ext
        · rfl
        change (1 - t) * f q + t * k q = a
        dsimp [t]
        field_simp [hgap.ne']
        ring
      refine ⟨(q, t), ⟨mem_univ _, ht⟩, ?_⟩
      simp only [Function.comp_apply, hcoord, N.coordinate_map_coordinate_inverse hx]
  rw [← hEq]
  exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (N.coordinate_map_smooth.continuousOn.comp hF.continuousOn hmem)

variable [T2Space M]

theorem frontier_closedGraphSlab_subset (f k : UnitTwoSphere → ℝ)
    (hf : Continuous f) (hk : Continuous k)
    (hfdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hkdom : ∀ q, k q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hfk : ∀ q, f q < k q) :
    frontier (N.closedGraphSlab f k) ⊆
      range (fun q => N.coordinate_map (q, f q)) ∪
        range (fun q => N.coordinate_map (q, k q)) := by
  have hclosed := (N.isCompact_closedGraphSlab f k hf hk hfdom hkdom hfk).isClosed
  intro x hx
  have hmem : x ∈ N.closedGraphSlab f k := hclosed.closure_eq ▸ hx.1
  by_cases hfEq : (N.coordinate_inverse x).2 = f (N.coordinate_inverse x).1
  · exact Or.inl ((N.mem_coordinate_graph_iff f hfdom).mpr ⟨hmem.1, hfEq⟩)
  by_cases hkEq : (N.coordinate_inverse x).2 = k (N.coordinate_inverse x).1
  · exact Or.inr ((N.mem_coordinate_graph_iff k hkdom).mpr ⟨hmem.1, hkEq⟩)
  have hopen := (N.isOpen_aboveGraph f hf).inter (N.isOpen_belowGraph k hk)
  have hsub : N.aboveGraph f ∩ N.belowGraph k ⊆ N.closedGraphSlab f k :=
    fun _ hy => ⟨hy.1.1, hy.1.2.le, hy.2.2.le⟩
  exfalso
  apply hx.2
  apply interior_mono hsub
  rw [hopen.interior_eq]
  exact ⟨⟨hmem.1, lt_of_le_of_ne hmem.2.1 (Ne.symm hfEq)⟩,
    ⟨hmem.1, lt_of_le_of_ne hmem.2.2 hkEq⟩⟩

end PoincareConjecture.EpsilonNeck
