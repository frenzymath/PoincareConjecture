import PoincareConjecture.Definitions.Ch12.StandardCap
import PoincareConjecture.Proofs.M34.Mathlib.ManifoldOpenMap

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

set_option backward.isDefEq.respectTransparency false in

theorem standardCylinderInner_pos (z : StandardCylinderSpace)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) (hv : v ≠ 0) :
    0 < standardCylinderInner 0 z v v := by
  have : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  let L := mvfderiv (𝓡 2) (fun q : UnitTwoSphere => q.1) z.1
  have hi : Function.Injective L := injective_mvfderiv_subtypeVal_sphere z.1
  have hnorm := sq_nonneg ‖L v.1‖
  have hsquare := sq_nonneg v.2
  by_contra h
  change ¬0 < 2 * (1 - 0) * inner ℝ (L v.1) (L v.1) + v.2 * v.2 at h
  have hle := le_of_not_gt h
  rw [real_inner_self_eq_norm_sq] at hle
  have hfirst : v.1 = 0 := hi (by
    rw [map_zero]
    apply norm_eq_zero.mp
    nlinarith)
  have hsecond : v.2 = 0 := by nlinarith
  exact hv (Prod.ext hfirst hsecond)

variable {g : RiemannianMetric 3 StandardCapSpace}

set_option backward.isDefEq.respectTransparency false in

theorem end_coordinate_mfderiv_bijective (e : StandardCylindricalEnd g)
    (z : StandardCylinderSpace) (hz : 0 ≤ z.2) :
    Function.Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate z) := by
  let L := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate z
  have hi : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro v hv
    by_contra hne
    have hpos := standardCylinderInner_pos z v hne
    have heq := e.metric_pullback z hz v v
    change g.inner (e.coordinate z) (L v) (L v) = _ at heq
    rw [hv] at heq
    simp only [map_zero] at heq
    linarith
  have hdim : Module.finrank ℝ (TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) =
      Module.finrank ℝ (TangentSpace (𝓡 3) (e.coordinate z)) := by
    simp [TangentSpace]
  let : FiniteDimensional ℝ (TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) := by
    unfold TangentSpace
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (e.coordinate z)) := by
    unfold TangentSpace
    infer_instance
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩

theorem end_coordinate_contMDiffAt (e : StandardCylindricalEnd g)
    {z : StandardCylinderSpace} (hz : 0 < z.2) :
    ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e.coordinate z := by
  apply e.coordinate_smooth.contMDiffAt
  apply (isOpen_univ.prod isOpen_Ioi).mem_nhds
  exact ⟨mem_univ _, by change -e.collar < z.2; linarith [e.collar_pos]⟩

theorem end_isOpen_coordinate_image (e : StandardCylindricalEnd g)
    {U : Set StandardCylinderSpace} (hU : IsOpen U) (hpos : ∀ z ∈ U, 0 < z.2) :
    IsOpen (e.coordinate '' U) := by
  apply isOpen_image_of_contMDiffOn_mfderiv_bijective
    (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (J := 𝓡 3) hU
  · intro z hz
    exact (end_coordinate_contMDiffAt e (hpos z hz)).contMDiffWithinAt
  · intro z hz
    exact end_coordinate_mfderiv_bijective e z (hpos z hz).le

theorem end_coordinate_mem_carrier (e : StandardCylindricalEnd g)
    {z : StandardCylinderSpace} (hz : 0 ≤ z.2) : e.coordinate z ∈ e.carrier := by
  rw [← e.coordinate_image]
  exact ⟨z, ⟨mem_univ _, hz⟩, rfl⟩

theorem end_inverse_contMDiffAt (e : StandardCylindricalEnd g)
    {z : StandardCylinderSpace} (hz : 0 < z.2) :
    ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.inverse (e.coordinate z) := by
  let U : Set StandardCylinderSpace := univ ×ˢ Ioi (0 : ℝ)
  have hU : IsOpen (e.coordinate '' U) :=
    end_isOpen_coordinate_image e (isOpen_univ.prod isOpen_Ioi) (fun _ h => h.2)
  have hsub : e.coordinate '' U ⊆ e.carrier := by
    rintro _ ⟨w, hw, rfl⟩
    exact end_coordinate_mem_carrier e hw.2.le
  exact (e.inverse_smooth.mono hsub).contMDiffAt
    (hU.mem_nhds ⟨z, ⟨mem_univ _, hz⟩, rfl⟩)

set_option backward.isDefEq.respectTransparency false in

theorem end_coordinate_inverse_mfderiv (e : StandardCylindricalEnd g)
    {z : StandardCylinderSpace} (hz : 0 < z.2)
    (u : TangentSpace (𝓡 3) (e.coordinate z)) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate z
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) u) = u := by
  have hleft : e.inverse (e.coordinate z) = z :=
    e.coordinate_left_inverse ⟨mem_univ _, hz.le⟩
  let U : Set StandardCylinderSpace := univ ×ˢ Ioi (0 : ℝ)
  have hU : IsOpen (e.coordinate '' U) :=
    end_isOpen_coordinate_image e (isOpen_univ.prod isOpen_Ioi) (fun _ h => h.2)
  have heq : e.coordinate ∘ e.inverse =ᶠ[𝓝 (e.coordinate z)] id := by
    filter_upwards [hU.mem_nhds ⟨z, ⟨mem_univ _, hz⟩, rfl⟩] with x hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact e.coordinate_right_inverse (end_coordinate_mem_carrier e hw.2.le)
  have hc : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      e.coordinate (e.inverse (e.coordinate z)) := by
    rw [hleft]
    exact (end_coordinate_contMDiffAt e hz).mdifferentiableAt (by simp)
  have hi := (end_inverse_contMDiffAt e hz).mdifferentiableAt (by simp)
  have hd := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp _ hc hi, mfderiv_id] at hd
  have hu := congrArg (fun L => L u) hd
  change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate
    (e.inverse (e.coordinate z))
    (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) u) = u at hu
  convert! hu using 1
  rw [hleft]

set_option backward.isDefEq.respectTransparency false in

theorem end_inverse_metric (e : StandardCylindricalEnd g)
    {z : StandardCylinderSpace} (hz : 0 < z.2)
    (u v : TangentSpace (𝓡 3) (e.coordinate z)) :
    g.inner (e.coordinate z) u v = standardCylinderInner 0 z
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) u)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) v) := by
  have h := e.metric_pullback z hz.le
    (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) u)
    (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) v)
  simpa only [end_coordinate_inverse_mfderiv e hz] using h

end PoincareConjecture.M34
