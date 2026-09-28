import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Cylinder.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Isotopy







set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.BalancedNeckChain

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem exists_openCylinderModel_of_middle_slice_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → ∀ D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace C.unionOpen ∞,
        ∀ j ∈ C.shape.active, ∀ c ∈ Ioo (-ε⁻¹) ε⁻¹,
        range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
          range (fun q : UnitTwoSphere => (C.neck j).coordinate_map (q, c)) →
        ∃ T : OpenCylinderModel (C.unionOpen : Set M),
          ∀ i ∈ C.shape.active, SmoothSphereIsotopicIn (C.unionOpen : Set M)
            (C.neck i).central_sphere T.middleSphere := by
  obtain ⟨ε₀, hε₀, hsmall, hisotopy⟩ := exists_central_spheres_isotopic_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε D j hj c hc hDzero
  obtain ⟨E, hEzero⟩ := (C.neck j).exists_unit_to_real_cylinder
  let q₀ := ((C.neck j).coordinate_inverse (C.neck j).center).1
  let T : OpenCylinderModel (C.unionOpen : Set M) :=
    OpenCylinderModel.ofDiffeomorph C.unionOpen (E.trans D) q₀
  have hmiddle : T.middleSphere =
      range (fun q : UnitTwoSphere => (C.neck j).coordinate_map (q, c)) := by
    dsimp only [T]
    rw [OpenCylinderModel.ofDiffeomorph_middleSphere, ← hDzero]
    congr 1
    funext q
    change (D (E ⟨(q, 1 / 2), mem_univ _, by norm_num⟩) : M) = _
    rw [hEzero q]
  have hc' : c ∈ Ioo (-(C.neck j).epsilon⁻¹) (C.neck j).epsilon⁻¹ := by
    simpa only [C.epsilon_eq j hj] using hc
  have hpos : 0 < (C.neck j).epsilon⁻¹ := inv_pos.mpr (C.neck j).epsilon_pos
  have hjcut : SmoothSphereIsotopicIn (C.unionOpen : Set M)
      (C.neck j).central_sphere
      (range (fun q : UnitTwoSphere => (C.neck j).coordinate_map (q, c))) := by
    have h := (C.neck j).coordinate_graphs_isotopic
      (fun _ => 0) (fun _ => c) contMDiff_const contMDiff_const
      (fun _ => ⟨neg_neg_of_pos hpos, hpos⟩) (fun _ => hc')
    rw [(C.neck j).centralSphere_range] at h
    exact h.mono fun x hx => mem_iUnion.mpr ⟨⟨j, hj⟩, hx⟩
  refine ⟨T, ?_⟩
  intro i hi
  rw [hmiddle]
  exact (hisotopy C hε i hi j hj).trans hjcut

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {ε : ℝ}

def tubeCertificateOfCylinder (C : BalancedNeckChain g ε) (hε : ε ≤ 1 / 200)
    (T : OpenCylinderModel (C.unionOpen : Set M))
    (hT : ∀ i ∈ C.shape.active, SmoothSphereIsotopicIn (C.unionOpen : Set M)
      (C.neck i).central_sphere T.middleSphere)
    (X : Set M) (hX : X ⊆ (C.unionOpen : Set M)) : EpsilonTubeCertificate g X where
  epsilon := ε
  epsilon_pos := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact C.epsilon_eq i hi ▸ (C.neck i).epsilon_pos
  epsilon_le_threshold := hε
  carrier := C.unionOpen
  carrier_open := C.unionOpen.isOpen
  contains_X := hX
  chain := C
  carrier_eq_chain_union := rfl
  cylinder := T
  central_sphere_isotopy := hT

end PoincareConjecture.BalancedNeckChain
