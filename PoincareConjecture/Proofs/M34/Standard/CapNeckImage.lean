import PoincareConjecture.Proofs.M34.Standard.CapNeckImageCoordinates

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X} (N : EpsilonNeck g)

noncomputable def imageShift (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    {epsilon c r : ℝ} (hepsilon : 0 < epsilon) (hepsilon' : epsilon < 1 / 2)
    (hdom : Ioo (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ⊆
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hsource : N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ⊆ e.source)
    (D : LeviCivitaData h) (q₀ : UnitTwoSphere) (hr : 0 < r)
    (hscalar : 0 < D.scalarCurvature (e (N.coordinate_map (q₀, c))))
    (hscale : r = D.scalarCurvature (e (N.coordinate_map (q₀, c))) ^ (-1 / 2 : ℝ))
    (hclose : RoundCylinderClose epsilon 0 (fun z v w => r⁻¹ ^ 2 *
      roundCylinderPullback h (fun z => e (N.coordinate_map (z.1, z.2 + c))) z v w)) :
    EpsilonNeck h := by
  let V := e '' N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c)
  let coordinate := (N.capShiftedCoordinate hdom).trans (N.capImageRegionHomeomorph e hsource)
  let coordinateMap : RoundCylinderSpace → X := fun z => e (N.coordinate_map (z.1, z.2 + c))
  let inverse : X → RoundCylinderSpace := fun x =>
    ((N.coordinate_inverse (e.symm x)).1, (N.coordinate_inverse (e.symm x)).2 - c)
  have hinv (x : X) (hx : x ∈ V) :
      e.symm x ∈ N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) := by
    obtain ⟨y, hy, rfl⟩ := hx
    simpa only [e.left_inv (hsource hy)] using hy
  have htarget : V ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hsource hx)
  have hinverse : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ inverse V := by
    have hN : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (N.coordinate_inverse ∘ e.symm) V :=
      N.coordinate_inverse_smooth.comp (hi.mono htarget) (fun x hx => (hinv x hx).1)
    have ht : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : RoundCylinderSpace => (z.1, z.2 - c)) :=
      contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)
    have htU : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : RoundCylinderSpace => (z.1, z.2 - c)) univ := ht.contMDiffOn
    exact htU.comp hN (fun _ _ => mem_univ _)
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr hepsilon), inv_pos.mpr hepsilon⟩
  refine {
    epsilon := epsilon
    epsilon_pos := hepsilon
    epsilon_lt_half := hepsilon'
    scale := r
    scale_pos := hr
    center := e (N.coordinate_map (q₀, c))
    connection := D
    scalar_center_pos := hscalar
    scale_eq_scalar := hscale
    carrier := V
    carrier_open := e.isOpen_image_of_subset_source (N.region_isOpen _ _) hsource
    coordinate := coordinate
    coordinate_map := coordinateMap
    coordinate_map_eq := fun _ => rfl
    coordinate_map_smooth := hf.comp (N.capShiftedCoordinate_contMDiffOn hdom)
      (fun _ hz => hsource (N.capShiftedCoordinate_mem hdom hz.2))
    coordinate_inverse := inverse
    coordinate_inverse_mem := ?_
    coordinate_inverse_left := ?_
    coordinate_inverse_right := ?_
    coordinate_inverse_smooth := hinverse
    central_sphere := e '' (N.coordinate_map '' (univ ×ˢ ({c} : Set ℝ)))
    central_sphere_eq := ?_
    center_on_central_sphere := ⟨N.coordinate_map (q₀, c),
      ⟨(q₀, c), ⟨mem_univ _, rfl⟩, rfl⟩, rfl⟩
    central_sphere_subset := ?_
    metric_comparison := ⟨hclose⟩
  }
  · intro x hx
    refine ⟨mem_univ _, ?_, ?_⟩ <;>
      dsimp only [inverse] <;> linarith [(hinv x hx).2.1, (hinv x hx).2.2]
  · intro z
    change ((N.coordinate_inverse (e.symm (e (N.coordinate_map (z.1, (z.2 : ℝ) + c))))).1,
      (N.coordinate_inverse (e.symm (e (N.coordinate_map (z.1, (z.2 : ℝ) + c))))).2 - c) = _
    rw [e.left_inv (hsource (N.capShiftedCoordinate_mem hdom
        (z := (z.1, (z.2 : ℝ))) z.2.property)),
      N.coordinate_inverse_coordinate_map_of_axial_mem
        (hdom ⟨by linarith [z.2.property.1], by linarith [z.2.property.2]⟩)]
    simp only [add_sub_cancel_right]
  · intro x hx
    apply Subtype.ext
    change e (N.coordinate_map ((N.coordinate_inverse (e.symm x)).1,
      (N.coordinate_inverse (e.symm x)).2 - c + c)) = x
    rw [sub_add_cancel, N.coordinate_map_coordinate_inverse (hinv x hx).1]
    exact e.right_inv (htarget hx)
  · ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨(z.1, 0), ⟨mem_univ _, rfl⟩, ?_⟩
      have hz' : z.2 = c := hz.2
      simp only [coordinateMap, zero_add, ← hz']
    · rintro ⟨z, hz, rfl⟩
      refine ⟨N.coordinate_map (z.1, c), ⟨(z.1, c), ⟨mem_univ _, rfl⟩, rfl⟩, ?_⟩
      have hz' : z.2 = 0 := hz.2
      simp only [coordinateMap, hz', zero_add]
  · rintro _ ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨N.coordinate_map z, ?_, rfl⟩
    have hz' : z.2 = c := hz.2
    simpa only [zero_add, ← hz'] using
      N.capShiftedCoordinate_mem hdom (z := (z.1, 0)) hzero

end PoincareConjecture.EpsilonNeck
