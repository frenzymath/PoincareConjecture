import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_relative_initial_angular_correction
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g)
    (e : OpenPartialHomeomorph RoundCylinderSpace M)
    (hsource : e.source = N.cylinderDomain)
    (htarget : e.target = N.carrier)
    (hsmooth : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source)
    (hinverse : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target)
    (hheight : ∀ z ∈ e.source, (N.coordinate_inverse (e z)).2 = z.2)
    (hzero : ∀ q : UnitTwoSphere, e (q, 0) = N.coordinate_map (q, 0)) :
    let L := N.epsilon⁻¹
    let rho : ℝ → ℝ := fun s =>
      (1 - Real.smoothTransition ((s + 3 * L / 4) / (L / 4))) * s
    let H : Set RoundCylinderSpace := univ ×ˢ Ioi (-L)
    ∃ A : OpenPartialHomeomorph RoundCylinderSpace RoundCylinderSpace,
      A.source = H ∧ A.target = H ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ A H ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ A.symm H ∧
      (∀ z ∈ H,
        A z = ((N.coordinate_inverse (e (z.1, rho z.2))).1, z.2) ∧
        A.symm z = ((e.symm (N.coordinate_map (z.1, rho z.2))).1, z.2)) ∧
      (∀ z ∈ H, (A z).2 = z.2 ∧ (A.symm z).2 = z.2) ∧
      (∀ z ∈ N.cylinderDomain, z.2 ≤ -(3 * L / 4) →
        A z = N.coordinate_inverse (e z) ∧
        A.symm z = e.symm (N.coordinate_map z)) ∧
      (∀ z ∈ H, -L / 2 ≤ z.2 → A z = z ∧ A.symm z = z) ∧
      (∀ upper : UnitTwoSphere → ℝ, (∀ q, L ≤ upper q) →
        let V : Set RoundCylinderSpace := {z | -L < z.2 ∧ z.2 < upper z.1}
        A '' V = V ∧ A.symm '' V = V ∧
        H ∩ A ⁻¹' V = V ∧ H ∩ A.symm ⁻¹' V = V) := by
  classical
  let L : ℝ := N.epsilon⁻¹
  let rho : ℝ → ℝ := fun s =>
    (1 - Real.smoothTransition ((s + 3 * L / 4) / (L / 4))) * s
  let H : Set RoundCylinderSpace := univ ×ˢ Ioi (-L)
  change ∃ A : OpenPartialHomeomorph RoundCylinderSpace RoundCylinderSpace,
    A.source = H ∧ A.target = H ∧
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ A H ∧
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ A.symm H ∧
    (∀ z ∈ H,
      A z = ((N.coordinate_inverse (e (z.1, rho z.2))).1, z.2) ∧
      A.symm z = ((e.symm (N.coordinate_map (z.1, rho z.2))).1, z.2)) ∧
    (∀ z ∈ H, (A z).2 = z.2 ∧ (A.symm z).2 = z.2) ∧
    (∀ z ∈ N.cylinderDomain, z.2 ≤ -(3 * L / 4) →
      A z = N.coordinate_inverse (e z) ∧
      A.symm z = e.symm (N.coordinate_map z)) ∧
    (∀ z ∈ H, -L / 2 ≤ z.2 → A z = z ∧ A.symm z = z) ∧
    (∀ upper : UnitTwoSphere → ℝ, (∀ q, L ≤ upper q) →
      let V : Set RoundCylinderSpace := {z | -L < z.2 ∧ z.2 < upper z.1}
      A '' V = V ∧ A.symm '' V = V ∧
      H ∩ A ⁻¹' V = V ∧ H ∩ A.symm ⁻¹' V = V)
  have hL : 0 < L := by
    dsimp [L]
    exact inv_pos.mpr N.epsilon_pos
  have hrho_smooth : ContDiff ℝ ∞ rho := by
    dsimp [rho]
    exact (contDiff_const.sub
      (Real.smoothTransition.contDiff.comp
        ((contDiff_id.add contDiff_const).div_const (L / 4)))).mul contDiff_id
  have hrho_low {s : ℝ} (hs : s ≤ -3 * L / 4) : rho s = s := by
    have harg : (s + 3 * L / 4) / (L / 4) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · positivity
    dsimp [rho]
    rw [Real.smoothTransition.zero_of_nonpos harg]
    ring
  have hrho_high {s : ℝ} (hs : -L / 2 ≤ s) : rho s = 0 := by
    have harg : 1 ≤ (s + 3 * L / 4) / (L / 4) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < L / 4)).2
      linarith
    dsimp [rho]
    rw [Real.smoothTransition.one_of_one_le harg]
    ring
  have hrho_mem {s : ℝ} (hs : -L < s) : rho s ∈ Ioo (-L) L := by
    by_cases hhigh : -L / 2 ≤ s
    · rw [hrho_high hhigh]
      constructor <;> linarith
    · have hsneg : s < -L / 2 := lt_of_not_ge hhigh
      let t : ℝ := Real.smoothTransition ((s + 3 * L / 4) / (L / 4))
      have ht0 : 0 ≤ t := Real.smoothTransition.nonneg _
      have ht1 : t ≤ 1 := Real.smoothTransition.le_one _
      have hcoef0 : 0 ≤ 1 - t := sub_nonneg.mpr ht1
      have hcoef1 : 1 - t ≤ 1 := by linarith
      have hsnonpos : 0 ≤ -s := by linarith
      have hlow : s ≤ (1 - t) * s := by
        nlinarith [mul_nonneg hcoef0 hsnonpos]
      have hsneg0 : s ≤ 0 := by linarith
      have hupper : (1 - t) * s ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hcoef0 hsneg0
      dsimp [rho, t]
      exact ⟨lt_of_lt_of_le hs hlow, lt_of_le_of_lt hupper (by linarith)⟩
  have hpair_mem {z : RoundCylinderSpace} (hz : z ∈ H) :
      (z.1, rho z.2) ∈ N.cylinderDomain := by
    exact ⟨mem_univ _, hrho_mem hz.2⟩
  have he_source {z : RoundCylinderSpace} (hz : z ∈ H) :
      (z.1, rho z.2) ∈ e.source := by
    rw [hsource]
    exact hpair_mem hz
  have he_target {z : RoundCylinderSpace} (hz : z ∈ H) :
      e (z.1, rho z.2) ∈ e.target := e.map_source (he_source hz)
  have hmap_mem {z : RoundCylinderSpace} (hz : z ∈ H) :
      N.coordinate_map (z.1, rho z.2) ∈ N.carrier :=
    N.coordinate_map_mem (hpair_mem hz)
  have hinverse_height {x : M} (hx : x ∈ e.target) :
      (e.symm x).2 = (N.coordinate_inverse x).2 := by
    have hs := hheight (e.symm x) (e.map_target hx)
    rw [e.right_inv hx] at hs
    exact hs.symm
  let forward : RoundCylinderSpace → RoundCylinderSpace := fun z =>
    ((N.coordinate_inverse (e (z.1, rho z.2))).1, z.2)
  let backward : RoundCylinderSpace → RoundCylinderSpace := fun z =>
    ((e.symm (N.coordinate_map (z.1, rho z.2))).1, z.2)
  have hforward_map {z : RoundCylinderSpace} (hz : z ∈ H) :
      forward z ∈ H := by
    exact ⟨mem_univ _, hz.2⟩
  have hbackward_map {z : RoundCylinderSpace} (hz : z ∈ H) :
      backward z ∈ H := by
    exact ⟨mem_univ _, hz.2⟩
  have hleft {z : RoundCylinderSpace} (hz : z ∈ H) :
      backward (forward z) = z := by
    have hw := hpair_mem hz
    have hes := he_source hz
    have hx := he_target hz
    have hxN : e (z.1, rho z.2) ∈ N.carrier := htarget ▸ hx
    have hh := hheight (z.1, rho z.2) hes
    have hcoord :
        ((N.coordinate_inverse (e (z.1, rho z.2))).1, rho z.2) =
          N.coordinate_inverse (e (z.1, rho z.2)) := by
      apply Prod.ext
      · rfl
      · exact hh.symm
    dsimp [forward, backward]
    rw [hcoord, N.coordinate_map_coordinate_inverse hxN, e.left_inv hes]
  have hright {z : RoundCylinderSpace} (hz : z ∈ H) :
      forward (backward z) = z := by
    have hw := hpair_mem hz
    have hx := hmap_mem hz
    have hes : e.symm (N.coordinate_map (z.1, rho z.2)) ∈ e.source :=
      e.map_target (htarget.symm ▸ hx)
    have hheight' := hinverse_height (htarget.symm ▸ hx)
    have hcoordN := N.coordinate_inverse_coordinate_map hw
    have hcoord :
        ((e.symm (N.coordinate_map (z.1, rho z.2))).1, rho z.2) =
          e.symm (N.coordinate_map (z.1, rho z.2)) := by
      apply Prod.ext
      · rfl
      · rw [hheight', hcoordN]
    dsimp [forward, backward]
    rw [hcoord, e.right_inv (htarget.symm ▸ hx), hcoordN]
  have hforward_high {z : RoundCylinderSpace} (hz : z ∈ H)
      (hs : -L / 2 ≤ z.2) : forward z = z := by
    have hr := hrho_high hs
    have hzero' := hzero z.1
    have hdom0 : (z.1, 0) ∈ N.cylinderDomain :=
      ⟨mem_univ _, N.zero_mem_interval⟩
    have hes0 : (z.1, 0) ∈ e.source := hsource.symm ▸ hdom0
    dsimp [forward]
    rw [hr, hzero', N.coordinate_inverse_coordinate_map hdom0]
  have hbackward_high {z : RoundCylinderSpace} (hz : z ∈ H)
      (hs : -L / 2 ≤ z.2) : backward z = z := by
    have hr := hrho_high hs
    have hzero' := hzero z.1
    have hdom0 : (z.1, 0) ∈ N.cylinderDomain :=
      ⟨mem_univ _, N.zero_mem_interval⟩
    have hes0 : (z.1, 0) ∈ e.source := hsource.symm ▸ hdom0
    dsimp [backward]
    rw [hr, ← hzero', e.left_inv hes0]
  have hforward_low {z : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain)
      (hs : z.2 ≤ -3 * L / 4) :
      forward z = N.coordinate_inverse (e z) := by
    have hr := hrho_low hs
    have hez : z ∈ e.source := hsource.symm ▸ hz
    have hh := hheight z hez
    dsimp [forward]
    rw [hr, Prod.eta z]
    apply Prod.ext
    · rfl
    · exact hh.symm
  have hbackward_low {z : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain)
      (hs : z.2 ≤ -3 * L / 4) :
      backward z = e.symm (N.coordinate_map z) := by
    have hr := hrho_low hs
    have hx : N.coordinate_map z ∈ N.carrier := N.coordinate_map_mem hz
    have hh := hinverse_height (htarget.symm ▸ hx)
    have hcoord := N.coordinate_inverse_coordinate_map hz
    dsimp [backward]
    rw [hr, Prod.eta z]
    apply Prod.ext
    · rfl
    · rw [hh, hcoord]
  have hpair_smooth :
      ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : RoundCylinderSpace => (z.1, rho z.2)) :=
    contMDiff_fst.prodMk (hrho_smooth.contMDiff.comp contMDiff_snd)
  have hforward_comp :
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : RoundCylinderSpace =>
          N.coordinate_inverse (e (z.1, rho z.2))) H := by
    have hecomp := hsmooth.comp hpair_smooth.contMDiffOn
      (fun z hz => he_source hz)
    have hcomp := N.coordinate_inverse_smooth.comp hecomp
      (fun z hz => by
        rw [← htarget]
        exact he_target hz)
    simpa only [Function.comp_def] using hcomp
  have hforward_smooth :
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ forward H := by
    have hfirst := contMDiff_fst.comp_contMDiffOn hforward_comp
    have hsecond : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun z : RoundCylinderSpace => z.2) H := contMDiff_snd.contMDiffOn
    have hp := hfirst.prodMk hsecond
    simpa only [forward, Function.comp_apply] using hp
  have hmap_comp :
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun z : RoundCylinderSpace =>
          N.coordinate_map (z.1, rho z.2)) H := by
    have hcomp := N.coordinate_map_smooth.comp hpair_smooth.contMDiffOn
      (fun z hz => hpair_mem hz)
    simpa only [Function.comp_def] using hcomp
  have hbackward_comp :
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : RoundCylinderSpace =>
          e.symm (N.coordinate_map (z.1, rho z.2))) H := by
    have hecomp := hinverse.comp hmap_comp
      (fun z hz => htarget.symm ▸ hmap_mem hz)
    simpa only [Function.comp_def] using hecomp
  have hbackward_smooth :
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ backward H := by
    have hfirst := contMDiff_fst.comp_contMDiffOn hbackward_comp
    have hsecond : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun z : RoundCylinderSpace => z.2) H := contMDiff_snd.contMDiffOn
    have hp := hfirst.prodMk hsecond
    simpa only [backward, Function.comp_apply] using hp
  let A : OpenPartialHomeomorph RoundCylinderSpace RoundCylinderSpace :=
    { toPartialEquiv :=
        { toFun := forward
          invFun := backward
          source := H
          target := H
          map_source' := fun _ hz => hforward_map hz
          map_target' := fun _ hz => hbackward_map hz
          left_inv' := fun z hz => hleft hz
          right_inv' := fun z hz => hright hz }
      open_source := isOpen_univ.prod isOpen_Ioi
      open_target := isOpen_univ.prod isOpen_Ioi
      continuousOn_toFun := hforward_smooth.continuousOn
      continuousOn_invFun := hbackward_smooth.continuousOn }
  have hVmap (upper : UnitTwoSphere → ℝ) (hupper : ∀ q, L ≤ upper q)
      {z : RoundCylinderSpace} (hz : z ∈ {z | -L < z.2 ∧ z.2 < upper z.1}) :
      forward z ∈ {z | -L < z.2 ∧ z.2 < upper z.1} := by
    have hzH : z ∈ H := ⟨mem_univ _, hz.1⟩
    by_cases hhigh : -L / 2 ≤ z.2
    · rw [hforward_high hzH hhigh]
      exact hz
    · have hsneg : z.2 < -L / 2 := lt_of_not_ge hhigh
      dsimp [forward]
      constructor
      · exact hz.1
      · have hu := hupper (N.coordinate_inverse (e (z.1, rho z.2))).1
        linarith
  have hVback (upper : UnitTwoSphere → ℝ) (hupper : ∀ q, L ≤ upper q)
      {z : RoundCylinderSpace} (hz : z ∈ {z | -L < z.2 ∧ z.2 < upper z.1}) :
      backward z ∈ {z | -L < z.2 ∧ z.2 < upper z.1} := by
    have hzH : z ∈ H := ⟨mem_univ _, hz.1⟩
    by_cases hhigh : -L / 2 ≤ z.2
    · rw [hbackward_high hzH hhigh]
      exact hz
    · have hsneg : z.2 < -L / 2 := lt_of_not_ge hhigh
      dsimp [backward]
      constructor
      · exact hz.1
      · have hu := hupper (e.symm (N.coordinate_map (z.1, rho z.2))).1
        linarith
  refine ⟨A, rfl, rfl, hforward_smooth, hbackward_smooth, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨rfl, rfl⟩
  · intro z hz
    exact ⟨rfl, rfl⟩
  · intro z hz hs
    have hs' : z.2 ≤ -3 * L / 4 := by linarith
    exact ⟨hforward_low hz hs', hbackward_low hz hs'⟩
  · intro z hz hs
    exact ⟨hforward_high hz hs, hbackward_high hz hs⟩
  · intro upper hupper
    let V : Set RoundCylinderSpace := {z | -L < z.2 ∧ z.2 < upper z.1}
    have hVforward : forward '' V = V := by
      apply Subset.antisymm
      · rintro y ⟨z, hz, rfl⟩
        exact hVmap upper hupper hz
      · intro y hy
        have hyH : y ∈ H := ⟨mem_univ _, hy.1⟩
        refine ⟨backward y, hVback upper hupper hy, ?_⟩
        exact hright hyH
    have hVbackward : backward '' V = V := by
      apply Subset.antisymm
      · rintro y ⟨z, hz, rfl⟩
        exact hVback upper hupper hz
      · intro y hy
        have hyH : y ∈ H := ⟨mem_univ _, hy.1⟩
        refine ⟨forward y, hVmap upper hupper hy, ?_⟩
        exact hleft hyH
    have hpre_forward : H ∩ forward ⁻¹' V = V := by
      ext z
      constructor
      · rintro ⟨hzH, hzV⟩
        have hz' := hVback upper hupper hzV
        rw [hleft hzH] at hz'
        change -L < z.2 ∧ z.2 < upper z.1 at hz'
        change -L < z.2 ∧ z.2 < upper z.1
        exact hz'
      · intro hzV
        exact ⟨⟨mem_univ _, hzV.1⟩, hVmap upper hupper hzV⟩
    have hpre_backward : H ∩ backward ⁻¹' V = V := by
      ext z
      constructor
      · rintro ⟨hzH, hzV⟩
        have hz' := hVmap upper hupper hzV
        rw [hright hzH] at hz'
        change -L < z.2 ∧ z.2 < upper z.1 at hz'
        change -L < z.2 ∧ z.2 < upper z.1
        exact hz'
      · intro hzV
        exact ⟨⟨mem_univ _, hzV.1⟩, hVback upper hupper hzV⟩
    change forward '' V = V ∧ backward '' V = V ∧
      H ∩ forward ⁻¹' V = V ∧ H ∩ backward ⁻¹' V = V
    exact ⟨hVforward, hVbackward, hpre_forward, hpre_backward⟩

end PoincareConjecture.EpsilonNeck
