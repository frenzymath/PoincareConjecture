import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.TwoSidedPartition
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Sphere
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.CylinderPasting











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CylinderGluing

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private def reflection : Diffeomorph CylModel CylModel
    RoundCylinderSpace RoundCylinderSpace ∞ where
  toFun p := (p.1, -p.2)
  invFun p := (p.1, -p.2)
  left_inv p := by simp
  right_inv p := by simp
  contMDiff_toFun := contMDiff_fst.prodMk contMDiff_snd.neg
  contMDiff_invFun := contMDiff_fst.prodMk contMDiff_snd.neg

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem exists_two_sided_cylinder (N : EpsilonNeck g) (hN : N.IsSeparating)
    (U V : Opens M) (hNU : N.carrier ⊆ U) (hNV : N.carrier ⊆ V)
    (F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace U ∞)
    (B : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace V ∞)
    (hF : (fun p : RoundCylinderSpace => (F p : M)) '' {p | p.2 ≤ 0} =
      {x | x ∈ N.carrier ∧ (N.coordinate_inverse x).2 ≤ 0})
    (hB : (fun p : RoundCylinderSpace => (B p : M)) '' {p | p.2 ≤ 0} =
      {x | x ∈ N.carrier ∧ 0 ≤ (N.coordinate_inverse x).2})
    (rF rB : ℝ) (hrF : 0 < rF) (hrB : 0 < rB)
    (hFcollar : ∀ p : RoundCylinderSpace, |p.2| < rF → (F p : M) = N.coordinate_map p)
    (hBcollar : ∀ p : RoundCylinderSpace, |p.2| < rB →
      (B p : M) = N.coordinate_map (p.1, -p.2)) :
    ∃ D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace ↥(U ⊔ V) ∞,
      (∀ q : UnitTwoSphere, (D (q, 0) : M) = N.coordinate_map (q, 0)) ∧
      range (fun q : UnitTwoSphere => (D (q, 0) : M)) = N.central_sphere := by
  let R := (fun p : RoundCylinderSpace => (F p : M)) '' {p | 0 < p.2}
  let L := (fun p : RoundCylinderSpace => (B p : M)) '' {p | 0 < p.2}
  obtain ⟨hRL, hRS, _, hcover, _⟩ := two_sided_partition N hN U V hNU hNV F B hF hB
  change Disjoint R L at hRL
  change Disjoint R N.central_sphere at hRS
  change (U : Set M) ∪ V = (R ∪ N.central_sphere) ∪ L at hcover
  let B' := reflection.trans B
  have hB' (p : RoundCylinderSpace) : (B' p : M) = B (p.1, -p.2) := rfl
  have hBzero (q : UnitTwoSphere) : (B (q, 0) : M) = N.coordinate_map (q, 0) := by
    simpa only [neg_zero] using hBcollar (q, 0) (by simpa only [abs_zero] using hrB)
  have hBhalf : (fun p : RoundCylinderSpace => (B' p : M)) '' {p | p.2 ≤ 0} =
      L ∪ N.central_sphere := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      change p.2 ≤ 0 at hp
      rcases lt_or_eq_of_le hp with hp | hp
      · exact Or.inl ⟨(p.1, -p.2), neg_pos.mpr hp, (hB' p).symm⟩
      · right
        change (B' p : M) ∈ N.central_sphere
        rw [hB', hp, neg_zero, hBzero, ← N.centralSphere_range]
        exact mem_range_self p.1
    · rintro (⟨p, hp, rfl⟩ | hx)
      · refine ⟨(p.1, -p.2), ?_, ?_⟩
        · change -p.2 ≤ 0
          exact neg_nonpos.mpr (le_of_lt hp)
        change (B' (p.1, -p.2) : M) = B p
        simp only [hB', neg_neg]
      · rw [← N.centralSphere_range] at hx
        obtain ⟨q, rfl⟩ := hx
        refine ⟨(q, 0), by change (0 : ℝ) ≤ 0; exact le_rfl, ?_⟩
        change (B' (q, 0) : M) = N.coordinate_map (q, 0)
        rw [hB', neg_zero, hBzero]
  have hagree (p : RoundCylinderSpace) (hp : |p.2| < min rF rB) : (B' p : M) = F p := by
    rw [hB', hBcollar (p.1, -p.2) (by simpa only [abs_neg] using hp.trans_le (min_le_right _ _)),
      neg_neg, hFcollar p (hp.trans_le (min_le_left _ _))]
  have hsep (p q : RoundCylinderSpace) (hp : p.2 ≤ 0) (hq : 0 < q.2) :
      (B' p : M) ≠ F q := by
    intro heq
    have hx : (B' p : M) ∈ L ∪ N.central_sphere := hBhalf ▸ mem_image_of_mem _ hp
    have hqR : (B' p : M) ∈ R := heq.symm ▸ mem_image_of_mem _ hq
    rcases hx with hx | hx
    · exact disjoint_left.mp hRL hqR hx
    · exact disjoint_left.mp hRS hqR hx
  obtain ⟨W, D, hD, hW⟩ := Poincare.exists_pasted_cylinder V U B' F
    (min rF rB) (lt_min hrF hrB) hagree hsep
  have hWsup : W = U ⊔ V := by
    apply SetLike.coe_injective
    rw [hBhalf] at hW
    change (W : Set M) = (U : Set M) ∪ V
    rw [hW, hcover]
    ext x
    simp only [mem_union]
    tauto
  have hzero (q : UnitTwoSphere) : (D (q, 0) : M) = N.coordinate_map (q, 0) := by
    rw [hD, if_pos le_rfl, hB', neg_zero, hBzero]
  have hout : ∃ D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace W ∞,
      (∀ q : UnitTwoSphere, (D (q, 0) : M) = N.coordinate_map (q, 0)) ∧
      range (fun q : UnitTwoSphere => (D (q, 0) : M)) = N.central_sphere := by
    refine ⟨D, hzero, ?_⟩
    rw [show (fun q : UnitTwoSphere => (D (q, 0) : M)) =
      (fun q => N.coordinate_map (q, 0)) from funext hzero, N.centralSphere_range]
  exact hWsup ▸ hout

end PoincareConjecture.CylinderGluing
