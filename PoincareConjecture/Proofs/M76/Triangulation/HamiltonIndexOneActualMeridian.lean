import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneActualMarkedArc
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneMeridian
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneMeridianBand

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (ℝ × V2)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "C8" => AddCircle (4 * (2 : ℝ))
local notation "Param" => Set.prod J Q

noncomputable def standardSquareMeridian (x : V2) : W :=
  (x 0, (-((x 1 + 7) / 4), -((x 1 + 7) / 4)))

private theorem coordinate_bound (x : Q) (i : Fin 2) : (x : V2) i ∈ J := by
  have h := (norm_le_pi_norm (x : V2) i).trans
    (mem_sphere_zero_iff_norm.mp x.property).le
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using h)

private theorem standard_meridian_radius (x : Q) :
    ‖(standardSquareMeridian (x : V2)).2‖ = ((x : V2) 1 + 7) / 4 := by
  have hx := coordinate_bound x 1
  have hr : 0 ≤ ((x : V2) 1 + 7) / 4 := by linarith [hx.1]
  change max ‖-(((x : V2) 1 + 7) / 4)‖ ‖-(((x : V2) 1 + 7) / 4)‖ = _
  simp only [max_self, norm_neg, Real.norm_eq_abs, abs_of_nonneg hr]

theorem exists_actual_marked_meridian_filling
    (A : W ≃ₜ W) (hAL : A '' squareBlock = squareBlock)
    (hAf : EqOn A id (frontier squareBlock)) {B T : Set W}
    (hB : IsFinitePLBallPair W B (T ∪ squareAttachingDisks))
    (hBL : B ⊆ squareBlock) (hT : IsClosed T)
    (hcontact : B ∩ frontier squareBlock = squareAttachingDisks)
    (hrims : T ∩ frontier squareBlock = squareRims)
    (tau : squareInnerAnnulus ≃ₜ T) (htau : tau.IsFinitePL)
    (hfix : ∀ x : squareInnerAnnulus, (x : W) ∈ squareRims → (tau x : W) = x)
    (unit : Param ≃ₜ T) (hunitPL : unit.IsFinitePL)
    (hunit : ∀ x : Param, ∀ hx : unitAnnulusCoordinates x ∈ squareInnerAnnulus,
      (tau ⟨unitAnnulusCoordinates x, hx⟩ : W) = unit x)
    (hKB : A '' squareUnitBlock ⊆ B) (hKT : Disjoint (A '' squareUnitBlock) T) :
    ∃ (marked : squareInnerAnnulus ≃ₜ T)
      (e : frontier squareShell ≃ₜ frontier (complementaryRegion B))
      (S : Set W) (gamma : Q ≃ₜ S)
      (F : C(closedBall (0 : V2) 1, complementaryRegion B)),
      marked.IsFinitePL ∧
      (∀ x : squareInnerAnnulus, (x : W) ∈ squareRims → (marked x : W) = x) ∧
      e.IsFinitePL ∧
      (∀ (x : squareInnerAnnulus) (hx : (x : W) ∈ frontier squareShell),
        (e ⟨x, hx⟩ : W) = marked x) ∧
      (∀ (x : squareOuterAnnulus) (hx : (x : W) ∈ frontier squareShell),
        (e ⟨x, hx⟩ : W) = x) ∧
      gamma.IsFinitePL ∧ S ⊆ frontier (complementaryRegion B) ∧
      (∀ x : Q, standardSquareMeridian x ∈ frontier squareShell) ∧
      (∀ (x : Q) (hx : standardSquareMeridian x ∈ frontier squareShell),
        (gamma x : W) = e ⟨standardSquareMeridian x, hx⟩) ∧
      ∀ x : Q, (F ⟨x, sphere_subset_closedBall x.property⟩ : W) = gamma x := by
  have hBclosed := hB.isCompact.isClosed
  have hBreg := hB.closure_interior_of_finrank_eq rfl
  have hBfront := hB.frontier_eq_of_finrank_eq rfl
  have hTL : T ⊆ squareBlock := by
    intro x hx
    apply hBL
    exact hBclosed.frontier_subset (hBfront.symm ▸ Or.inl hx)
  obtain ⟨_, _, hEfront⟩ := complementaryRegion_geometry
    hBclosed hBreg hBL hT hBfront hcontact hrims
  obtain ⟨marked, f, ellI, hmPL, hmfix, hfPL, hfinj, hfT, hfsection,
    hfm, hfp, hfmface, hfpface, hfouter, helm, help, hfpolar⟩ :=
    exists_actual_zero_winding_marked_arc A hAL hAf hTL hrims
      tau htau hfix unit hunitPL hunit hKT
  let a := meridianProductCoordinates
  let fV : ℝ → V := fun s => a.symm (f s)
  have hfV : FinitePiecewiseAffineOn fV J := hfPL.postcomp a.symm.toContinuousAffineMap
  have hfinjV : InjOn fV J := by
    intro s hs t ht heq
    exact hfinj hs ht (a.symm.injective heq)
  let u0 : Q := squareCircle (0 : C8)
  have hfmV : fV (-1) = (-1, (3 / 2 : ℝ) • (u0 : V2)) := by
    change a.symm (f (-1)) = _
    rw [hfm]
    change (-1, ![-(3 / 2 : ℝ), -(3 / 2 : ℝ)]) =
      (-1, (3 / 2 : ℝ) • (squareCircle (0 : C8) : V2))
    rw [squareCircle_zero]
    congr 1
    ext i
    fin_cases i <;> norm_num
  have hfpV : fV 1 = (1, (3 / 2 : ℝ) • (u0 : V2)) := by
    change a.symm (f 1) = _
    rw [hfp]
    change (1, ![-(3 / 2 : ℝ), -(3 / 2 : ℝ)]) =
      (1, (3 / 2 : ℝ) • (squareCircle (0 : C8) : V2))
    rw [squareCircle_zero]
    congr 1
    ext i
    fin_cases i <;> norm_num
  have houterV (s : ℝ) (hs : s ∈ J) : ‖(fV s).2‖ < 2 := by
    have hn := freeCoordinates_norm (fV s).2
    change ‖(f s).2‖ = ‖(fV s).2‖ at hn
    rw [← hn]
    exact hfouter s hs
  obtain ⟨SV, gammaV, ell, hgammaV, hbottom, hother, hellbottom, hellother⟩ :=
    exists_marked_meridian u0 fV hfV hfinjV hfmV hfpV hfmface hfpface
      houterV ellI helm help
  let S : Set W := a '' SV
  let gamma : Q ≃ₜ S := gammaV.trans (a.toHomeomorph.image SV)
  have hgamma : gamma.IsFinitePL := by
    obtain ⟨g, hg, hgeq⟩ := hgammaV
    exact ⟨fun x => a (g x), hg.postcomp a.toContinuousAffineMap,
      fun x => congrArg a (hgeq x)⟩
  obtain ⟨e0, he0, heinner, heouter⟩ :=
    exists_marked_shell_frontier_map marked hmPL hrims hmfix
  let e := e0.trans (Homeomorph.setCongr hEfront.symm)
  have he : e.IsFinitePL := by
    obtain ⟨g, hg, hgeq⟩ := he0
    exact ⟨g, hg, hgeq⟩
  obtain ⟨band, _, _, hband, hbandzero, _⟩ := exists_standard_meridian_band
  have hstandard (x : Q) : standardSquareMeridian x ∈ frontier squareShell := by
    have h := hband (show ((x : V2), (0 : ℝ)) ∈
      Q ×ˢ Icc (-(1 / 4 : ℝ)) (1 / 4) from ⟨x.property, by norm_num⟩)
    rw [hbandzero x] at h
    exact h
  have hstandardInner (x : Q) (hx : (x : V2) 1 = -1) :
      standardSquareMeridian x ∈ squareInnerAnnulus := by
    refine ⟨coordinate_bound x 0, mem_sphere_zero_iff_norm.mpr ?_⟩
    rw [standard_meridian_radius, hx]
    norm_num
  have hstandardOuter (x : Q) (hx : (x : V2) 1 ≠ -1) :
      standardSquareMeridian x ∈ squareOuterAnnulus := by
    have h := squareShell_frontier ▸ hstandard x
    apply h.resolve_left
    intro hi
    have hn := mem_sphere_zero_iff_norm.mp hi.2
    rw [standard_meridian_radius] at hn
    exact hx (by linarith)
  have hgammaBottom (x : Q) (hx : (x : V2) 1 = -1) :
      (gamma x : W) = f ((x : V2) 0) := by
    change a (gammaV x : V) = _
    rw [hbottom x hx]
    exact a.apply_symm_apply _
  have hgammaOther (x : Q) (hx : (x : V2) 1 ≠ -1) :
      (gamma x : W) = standardSquareMeridian x := by
    change a (gammaV x : V) = _
    rw [hother x hx]
    change ((x : V2) 0,
      ((1 / 4 : ℝ) * ((x : V2) 1 + 7)) •
        ((squareCircle (0 : C8) : V2) 0, (squareCircle (0 : C8) : V2) 1)) = _
    rw [squareCircle_zero]
    apply Prod.ext
    · rfl
    · apply Prod.ext <;>
        change ((1 / 4 : ℝ) * ((x : V2) 1 + 7)) * (-1) =
          -(((x : V2) 1 + 7) / 4) <;> ring
  have hmarked (x : Q) (hx : standardSquareMeridian x ∈ frontier squareShell) :
      (gamma x : W) = e ⟨standardSquareMeridian x, hx⟩ := by
    by_cases hxb : (x : V2) 1 = -1
    · rw [hgammaBottom x hxb]
      let s : J := ⟨(x : V2) 0, coordinate_bound x 0⟩
      have hv : unitAnnulusCoordinates ((s : ℝ), (squareCircle (0 : C8) : V2)) =
          standardSquareMeridian x := by
        rw [unitAnnulusCoordinates_apply, squareCircle_zero]
        change ((x : V2) 0, (3 / 2 : ℝ) • (-1, -1)) =
          ((x : V2) 0, (-(((x : V2) 1 + 7) / 4), -(((x : V2) 1 + 7) / 4)))
        rw [hxb]
        norm_num
      have hi := hstandardInner x hxb
      have hf := hfsection s (hv.symm ▸ hi)
      have hsub : (⟨unitAnnulusCoordinates ((s : ℝ),
          (squareCircle (0 : C8) : V2)), hv.symm ▸ hi⟩ : squareInnerAnnulus) =
          ⟨standardSquareMeridian x, hi⟩ := Subtype.ext hv
      rw [hsub] at hf
      exact hf.trans (heinner ⟨standardSquareMeridian x, hi⟩ hx).symm
    · rw [hgammaOther x hxb]
      exact (heouter ⟨standardSquareMeridian x, hstandardOuter x hxb⟩ hx).symm
  have hS : S ⊆ frontier (complementaryRegion B) := by
    intro y hy
    obtain ⟨x, hx⟩ := gamma.surjective ⟨y, hy⟩
    have h := (e ⟨standardSquareMeridian x, hstandard x⟩).property
    rw [← hmarked x (hstandard x)] at h
    have hg : (gamma x : W) = y := congrArg Subtype.val hx
    rwa [hg] at h
  let gammaE : C(Q, complementaryRegion B) :=
    ⟨fun x => ⟨gamma x, (isClosed_closure : IsClosed (complementaryRegion B)).frontier_subset
      (hS (gamma x).property)⟩,
      (continuous_subtype_val.comp gamma.continuous).subtype_mk _⟩
  have hangle (x : Q) : (A.symm (gammaE x : W)).2 =
      ‖(A.symm (gammaE x : W)).2‖ •
        ((squareCircle ((ell x : ℝ) : C8) : V2) 0,
          (squareCircle ((ell x : ℝ) : C8) : V2) 1) := by
    change (A.symm (gamma x : W)).2 = ‖(A.symm (gamma x : W)).2‖ • _
    by_cases hxb : (x : V2) 1 = -1
    · let s : J := ⟨(x : V2) 0, coordinate_bound x 0⟩
      rw [hgammaBottom x hxb, hellbottom x s rfl hxb]
      exact hfpolar s
    · rw [hgammaOther x hxb, hellother x hxb, AddCircle.coe_zero, squareCircle_zero]
      have hAi : A.symm (standardSquareMeridian x) = standardSquareMeridian x := by
        apply A.injective
        rw [A.apply_symm_apply]
        exact (hAf (hstandardOuter x hxb).1).symm
      rw [hAi, standard_meridian_radius]
      change (-(((x : V2) 1 + 7) / 4), -(((x : V2) 1 + 7) / 4)) =
        (((x : V2) 1 + 7) / 4) • (-1, -1)
      apply Prod.ext <;> simp
  obtain ⟨hEE0, r, hr⟩ := exists_same_A_complement_retraction A hAL hAf hB hBL hT
    hcontact hrims tau htau hfix hKB hKT
  obtain ⟨F, hF⟩ := exists_physical_retracted_disk_filling A hAL
    (complementaryRegion B) hEE0 r hr gammaE ell hangle
  refine ⟨marked, e, S, gamma, F, hmPL, hmfix, he, heinner, heouter,
    hgamma, hS, hstandard, hmarked, ?_⟩
  intro x
  exact congrArg Subtype.val (hF x)

end PoincareConjecture.M76.HamiltonIndexOne
