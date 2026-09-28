import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneAnnulusTwist
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOnePhysicalFilling










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

private theorem unit_parameter_mem (x : Param) :
    unitAnnulusCoordinates x ∈ squareInnerAnnulus := by
  refine ⟨x.property.1, mem_sphere_zero_iff_norm.mpr ?_⟩
  change ‖(3 / 2 : ℝ) • ((x : V).2 0, (x : V).2 1)‖ = 3 / 2
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), freeCoordinates_norm,
    mem_sphere_zero_iff_norm.mp x.property.2, mul_one]

private theorem rims_inner {x : W} (hx : x ∈ squareRims) : x ∈ squareInnerAnnulus := by
  refine ⟨?_, hx.2⟩
  rcases hx.1 with hx | hx
  · change x.1 = -1 at hx
    rw [hx]
    norm_num
  · change x.1 = 1 at hx
    rw [hx]
    norm_num

private theorem block_face {x : W} (hx : x ∈ squareBlock)
    (hs : x.1 = -1 ∨ x.1 = 1) : x ∈ frontier squareBlock := by
  refine ⟨subset_closure hx, ?_⟩
  intro hi
  rw [squareBlock, interior_prod_eq, interior_Icc] at hi
  rcases hs with hs | hs
  · exact (lt_irrefl (-1 : ℝ)) (hs ▸ hi.1.1)
  · exact (lt_irrefl (1 : ℝ)) (hs ▸ hi.1.2)





theorem exists_actual_zero_winding_marked_arc
    (A : W ≃ₜ W) (hAL : A '' squareBlock = squareBlock)
    (hAf : EqOn A id (frontier squareBlock)) {T : Set W}
    (hTL : T ⊆ squareBlock) (hrims : T ∩ frontier squareBlock = squareRims)
    (tau : squareInnerAnnulus ≃ₜ T) (htau : tau.IsFinitePL)
    (hfix : ∀ x : squareInnerAnnulus, (x : W) ∈ squareRims → (tau x : W) = x)
    (unit : Param ≃ₜ T) (hunitPL : unit.IsFinitePL)
    (hunit : ∀ x : Param, ∀ hx : unitAnnulusCoordinates x ∈ squareInnerAnnulus,
      (tau ⟨unitAnnulusCoordinates x, hx⟩ : W) = unit x)
    (hKT : Disjoint (A '' squareUnitBlock) T) :
    ∃ (marked : squareInnerAnnulus ≃ₜ T) (f : ℝ → W) (ell : C(J, ℝ)),
      marked.IsFinitePL ∧
      (∀ x : squareInnerAnnulus, (x : W) ∈ squareRims → (marked x : W) = x) ∧
      FinitePiecewiseAffineOn f J ∧ InjOn f J ∧
      (∀ s : J, f s ∈ T) ∧
      (∀ (s : J) (hx : unitAnnulusCoordinates
          ((s : ℝ), (squareCircle (0 : C8) : V2)) ∈ squareInnerAnnulus),
        f s = marked ⟨unitAnnulusCoordinates
          ((s : ℝ), (squareCircle (0 : C8) : V2)), hx⟩) ∧
      f (-1) = (-1, (-(3 / 2), -(3 / 2))) ∧
      f 1 = (1, (-(3 / 2), -(3 / 2))) ∧
      (∀ s ∈ J, (f s).1 = -1 → s = -1) ∧
      (∀ s ∈ J, (f s).1 = 1 → s = 1) ∧
      (∀ s ∈ J, ‖(f s).2‖ < 2) ∧
      ell ⟨-1, by norm_num⟩ = 0 ∧ ell ⟨1, by norm_num⟩ = 0 ∧
      ∀ s : J, (A.symm (f s)).2 = ‖(A.symm (f s)).2‖ •
        ((squareCircle ((ell s : ℝ) : C8) : V2) 0,
          (squareCircle ((ell s : ℝ) : C8) : V2) 1) := by
  have hTE : T ⊆ coreExterior (A '' squareUnitBlock) := by
    intro x hx
    exact subset_closure ⟨hTL hx, fun hk => Set.disjoint_left.mp hKT hk hx⟩
  obtain ⟨rho, hpolar, hrho⟩ := exists_actual_core_angular_map A hAL hAf
  let c := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  have hnorm (w : ℝ × ℝ) : ‖c.symm w‖ = ‖w‖ := by
    have h := freeCoordinates_norm (c.symm w)
    change ‖c (c.symm w)‖ = ‖c.symm w‖ at h
    rw [c.apply_symm_apply] at h
    exact h.symm
  let j : C(J × Q, coreExterior (A '' squareUnitBlock)) :=
    ⟨fun z => ⟨unit ⟨((z.1 : ℝ), (z.2 : V2)), z.1.property, z.2.property⟩,
      hTE (unit _).property⟩,
      ((continuous_subtype_val.comp unit.continuous).comp
        (Homeomorph.Set.prod J Q).symm.continuous).subtype_mk _⟩
  let rhoU : C(J × Q, Q) :=
    ⟨fun z => ⟨c.symm (rho (j z) : ℝ × ℝ), mem_sphere_zero_iff_norm.mpr (by
      rw [hnorm, mem_sphere_zero_iff_norm.mp (rho (j z)).property])⟩,
      (c.symm.continuous.comp
        (continuous_subtype_val.comp (rho.continuous.comp j.continuous))).subtype_mk _⟩
  have hunitEnd (x : Param) (hx : (x : V).1 = -1 ∨ (x : V).1 = 1) :
      (unit x : W) = unitAnnulusCoordinates x := by
    refine (hunit x (unit_parameter_mem x)).symm.trans (hfix _ ?_)
    refine ⟨?_, (unit_parameter_mem x).2⟩
    change (x : V).1 ∈ ({-1, 1} : Set ℝ)
    simpa only [mem_insert_iff, mem_singleton_iff] using hx
  have hend (s : J) (hs : (s : ℝ) = -1 ∨ (s : ℝ) = 1) (u : Q) : rhoU (s, u) = u := by
    let u' : sphere (0 : ℝ × ℝ) 1 := ⟨c (u : V2), mem_sphere_zero_iff_norm.mpr (by
      rw [show ‖c (u : V2)‖ = ‖(u : V2)‖ from freeCoordinates_norm u,
        mem_sphere_zero_iff_norm.mp u.property])⟩
    have hj : (j (s, u) : W) = ((s : ℝ), (3 / 2 : ℝ) • (u' : ℝ × ℝ)) :=
      hunitEnd ⟨((s : ℝ), (u : V2)), s.property, u.property⟩ hs
    have h := hrho s hs u' (j (s, u)) hj
    apply Subtype.ext
    change c.symm (rho (j (s, u)) : ℝ × ℝ) = (u : V2)
    rw [h]
    exact c.symm_apply_apply (u : V2)
  obtain ⟨m, markedU, f, ell, hmPL, hfPL, hfinj, hfmarked, hfunit,
    hmfix, hfminus, hfplus, helm, help, hang⟩ :=
    exists_zero_winding_marked_annulus unit hunitPL rhoU
      (hend ⟨-1, by norm_num⟩ (Or.inl rfl))
      (hend ⟨1, by norm_num⟩ (Or.inr rfl))
  let v : Param ≃ₜ squareInnerAnnulus := unit.trans tau.symm
  have hvPL : v.IsFinitePL := hunitPL.trans htau.symm
  have hvval (x : Param) : (v x : W) = unitAnnulusCoordinates x := by
    have h : tau (v x) = tau ⟨unitAnnulusCoordinates x, unit_parameter_mem x⟩ := by
      change tau (tau.symm (unit x)) = _
      rw [tau.apply_symm_apply]
      exact Subtype.ext (hunit x (unit_parameter_mem x)).symm
    exact congrArg Subtype.val (tau.injective h)
  let marked := v.symm.trans markedU
  have hmfixR (x : squareInnerAnnulus) (hx : (x : W) ∈ squareRims) :
      (marked x : W) = x := by
    let u := v.symm x
    have huval : unitAnnulusCoordinates u = (x : W) :=
      (hvval u).symm.trans (congrArg Subtype.val (v.apply_symm_apply x))
    have hs : (u : V).1 = -1 ∨ (u : V).1 = 1 := by
      have hfst := congrArg Prod.fst huval
      change (u : V).1 = (x : W).1 at hfst
      rw [hfst]
      simpa only [mem_insert_iff, mem_singleton_iff] using hx.1
    change (markedU u : W) = (x : W)
    rw [hmfix u hs, hunitEnd u hs, huval]
  have hfT (s : J) : f s ∈ T := by
    rw [hfunit s]
    exact (unit _).property
  have hsource_face (x : Param) (hx : (unit x : W) ∈ squareRims) :
      (x : V).1 = (unit x : W).1 := by
    let y : squareInnerAnnulus := ⟨unit x, rims_inner hx⟩
    have hy : tau y = unit x := Subtype.ext (hfix y hx)
    have hv : (v x : W) = (unit x : W) := by
      change (tau.symm (unit x) : W) = _
      rw [← hy, tau.symm_apply_apply]
      exact (hfix y hx).symm
    exact congrArg Prod.fst ((hvval x).symm.trans hv)
  have hfside (s : J) (b : ℝ) (hb : b = -1 ∨ b = 1) (hs : (f s).1 = b) :
      (s : ℝ) = b := by
    let x : Param := ⟨((s : ℝ),
      (squareCircle ((-4 * (m : ℝ) * ((s : ℝ) + 1) : ℝ) : C8) : V2)),
        s.property, (squareCircle _).property⟩
    have hx : (unit x : W) ∈ squareRims := by
      rw [← hfunit s]
      exact hrims ▸ ⟨hfT s, block_face (hTL (hfT s)) (by rwa [hs])⟩
    have h := hsource_face x hx
    change (s : ℝ) = (unit x : W).1 at h
    rw [← hfunit s] at h
    exact h.trans hs
  have houter (x : W) (hx : x ∈ T) : ‖x.2‖ < 2 := by
    have hle := mem_closedBall_zero_iff.mp (hTL hx).2
    apply lt_of_le_of_ne hle
    intro heq
    have hf : x ∈ frontier squareBlock := by
      refine ⟨subset_closure (hTL hx), ?_⟩
      intro hi
      rw [squareBlock, interior_prod_eq, interior_closedBall _ (by norm_num)] at hi
      have hi2 := mem_ball_zero_iff.mp hi.2
      linarith
    have hr : x ∈ squareRims := hrims ▸ ⟨hx, hf⟩
    have hn := mem_sphere_zero_iff_norm.mp hr.2
    linarith
  refine ⟨marked, f, ell, hvPL.symm.trans hmPL, hmfixR, hfPL, hfinj, hfT,
    ?_, ?_, ?_, ?_, ?_, ?_, helm, help, ?_⟩
  · intro s hx
    let x : Param := ⟨((s : ℝ), (squareCircle (0 : C8) : V2)),
      s.property, (squareCircle _).property⟩
    have hxv : (⟨unitAnnulusCoordinates x, hx⟩ : squareInnerAnnulus) = v x :=
      Subtype.ext (hvval x).symm
    rw [hxv]
    change f s = markedU (v.symm (v x))
    rw [v.symm_apply_apply]
    exact hfmarked s
  · rw [hfminus, hunitEnd _ (Or.inl rfl)]
    change (-1, (3 / 2 : ℝ) •
      ((squareCircle (0 : C8) : V2) 0, (squareCircle (0 : C8) : V2) 1)) = _
    rw [squareCircle_zero]
    norm_num
  · rw [hfplus, hunitEnd _ (Or.inr rfl)]
    change (1, (3 / 2 : ℝ) •
      ((squareCircle (0 : C8) : V2) 0, (squareCircle (0 : C8) : V2) 1)) = _
    rw [squareCircle_zero]
    norm_num
  · intro s hs hf
    exact hfside ⟨s, hs⟩ (-1) (Or.inl rfl) hf
  · intro s hs hf
    exact hfside ⟨s, hs⟩ 1 (Or.inr rfl) hf
  · intro s hs
    exact houter (f s) (hfT ⟨s, hs⟩)
  · intro s
    let z : J × Q := (s,
      squareCircle ((-4 * (m : ℝ) * ((s : ℝ) + 1) : ℝ) : C8))
    have hj : (j z : W) = f s := (hfunit s).symm
    have hdir : (rho (j z) : ℝ × ℝ) =
        c (squareCircle ((ell s : ℝ) : C8) : V2) := by
      have h := congrArg (fun u : Q => c (u : V2)) (hang s)
      change c (c.symm (rho (j z) : ℝ × ℝ)) = _ at h
      simpa only [c.apply_symm_apply] using h
    have hp := hpolar (j z)
    rw [hdir, hj] at hp
    exact hp

end PoincareConjecture.M76.HamiltonIndexOne
