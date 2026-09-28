









import PoincareConjecture.Proofs.M05.Analysis.ODE.LocalFlow.Inhomogeneous


noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal ContDiff

namespace Poincare.ODE.LocalFlow

section VariationalSolution

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

noncomputable local instance parametricLinearODEEndoNormedAddCommGroup :
    NormedAddCommGroup (G →L[ℝ] G) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance parametricLinearODEEndoNormedSpace :
    NormedSpace ℝ (G →L[ℝ] G) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance parametricLinearODEDerivativeNormedAddCommGroup :
    NormedAddCommGroup (F →L[ℝ] G →L[ℝ] G) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance parametricLinearODEDerivativeNormedSpace :
    NormedSpace ℝ (F →L[ℝ] G →L[ℝ] G) :=
  ContinuousLinearMap.toNormedSpace

noncomputable def variationalForcing
    (A : F → ℝ → (G →L[ℝ] G)) (a b' h₀ : ℝ) (Z₀ : F → G)
    (x : F) (v : F) (t : ℝ) : G :=
  (fderiv ℝ (fun y => A y t) x) v (linearODESolution A a b' h₀ Z₀ x t)

noncomputable def variationalSolution
    (A : F → ℝ → (G →L[ℝ] G)) (a b' h₀ : ℝ) (Z₀ : F → G)
    (x : F) (v : F) : ℝ → G :=
  inhomogLinearODESolution A (fun y t => variationalForcing A a b' h₀ Z₀ y v t)
    a b' h₀ (fun y => (fderiv ℝ Z₀ y) v) x

omit [CompleteSpace G] in
theorem variationalW_init
    (A : F → ℝ → (G →L[ℝ] G)) (a b' h₀ : ℝ) (Z₀ : F → G) (x : F) (v : F) :
    variationalSolution A a b' h₀ Z₀ x v h₀ = (fderiv ℝ Z₀ x) v := by
  unfold variationalSolution
  exact inhomogLinearODESolution_init _ _ _ _ _ _ _

theorem variationalForcing_continuousOn
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U) (v : F) :
    ContinuousOn (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') := by
  have hZ_cont : ContinuousOn (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b') :=
    linearODESolution_continuousOn h₀_mem hU hA_cont hZ₀_cont
  have happ : ContinuousOn
      (Function.uncurry fun x t => (fderiv ℝ (fun y => A y t) x) v)
      (U ×ˢ Set.Ioo a b') := by
    exact ContinuousOn.clm_apply hDA_cont continuousOn_const
  have hgoal : ContinuousOn
      (fun p : F × ℝ =>
        ((fderiv ℝ (fun y => A y p.2) p.1) v)
          (linearODESolution A a b' h₀ Z₀ p.1 p.2))
      (U ×ˢ Set.Ioo a b') :=
    ContinuousOn.clm_apply happ hZ_cont
  refine hgoal.congr ?_
  intro p _
  unfold variationalForcing
  rfl

theorem variationalW_hasDerivAt
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) (v : F) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    HasDerivAt (variationalSolution A a b' h₀ Z₀ x v ·)
      ((fderiv ℝ (fun y => A y t) x) v (linearODESolution A a b' h₀ Z₀ x t)
        + A x t (variationalSolution A a b' h₀ Z₀ x v t)) t := by
  have hb_cont : ContinuousOn
      (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') :=
    variationalForcing_continuousOn h₀_mem hU hA_cont hDA_cont hZ₀_cont v
  have hderiv : HasDerivAt
      (inhomogLinearODESolution A
        (fun y t => variationalForcing A a b' h₀ Z₀ y v t) a b' h₀
        (fun y => (fderiv ℝ Z₀ y) v) x ·)
      (A x t (inhomogLinearODESolution A
          (fun y t => variationalForcing A a b' h₀ Z₀ y v t) a b' h₀
          (fun y => (fderiv ℝ Z₀ y) v) x t)
        + variationalForcing A a b' h₀ Z₀ x v t) t :=
    inhomogLinearODESolution_hasDerivAt h₀_mem hA_cont hb_cont hx ht
  have hderiv' : HasDerivAt
      (inhomogLinearODESolution A
        (fun y t => variationalForcing A a b' h₀ Z₀ y v t) a b' h₀
        (fun y => (fderiv ℝ Z₀ y) v) x ·)
      (variationalForcing A a b' h₀ Z₀ x v t
        + A x t (inhomogLinearODESolution A
          (fun y t => variationalForcing A a b' h₀ Z₀ y v t) a b' h₀
          (fun y => (fderiv ℝ Z₀ y) v) x t)) t := by
    have := hderiv
    rwa [add_comm] at this
  exact hderiv'

theorem variationalW_continuousOn
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    (v : F)
    (hZ₀'_cont : ContinuousOn (fun x => (fderiv ℝ Z₀ x) v) U) :
    ContinuousOn
      (Function.uncurry (fun x t => variationalSolution A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') := by
  have hb_cont : ContinuousOn
      (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') :=
    variationalForcing_continuousOn h₀_mem hU hA_cont hDA_cont hZ₀_cont v
  exact inhomogLinearODESolution_continuousOn (Z₀ := fun y => (fderiv ℝ Z₀ y) v)
    h₀_mem hU hA_cont hb_cont hZ₀'_cont

theorem inhomogLinearODE_unique_on_Ioo
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {A : ℝ → (G →L[ℝ] G)} {b : ℝ → G} {a b' h₀ : ℝ}
    (ht₀ : h₀ ∈ Set.Ioo a b')
    (hA_cont : ContinuousOn A (Set.Ioo a b'))
    {Z₁ Z₂ : ℝ → G}
    (hZ₁ : ∀ t ∈ Set.Ioo a b', HasDerivAt Z₁ (A t (Z₁ t) + b t) t)
    (hZ₂ : ∀ t ∈ Set.Ioo a b', HasDerivAt Z₂ (A t (Z₂ t) + b t) t)
    (heq : Z₁ h₀ = Z₂ h₀) :
    Set.EqOn Z₁ Z₂ (Set.Ioo a b') := by
  set D : ℝ → G := fun t => Z₁ t - Z₂ t with hD_def
  have hD_deriv : ∀ t ∈ Set.Ioo a b', HasDerivAt D (A t (D t)) t := by
    intro t ht
    have h₁ : HasDerivAt Z₁ (A t (Z₁ t) + b t) t := hZ₁ t ht
    have h₂ : HasDerivAt Z₂ (A t (Z₂ t) + b t) t := hZ₂ t ht
    have hsub : HasDerivAt D ((A t (Z₁ t) + b t) - (A t (Z₂ t) + b t)) t := h₁.sub h₂
    have h_eq : (A t (Z₁ t) + b t) - (A t (Z₂ t) + b t) = A t (D t) := by
      have hD_t : D t = Z₁ t - Z₂ t := rfl
      rw [hD_t, ContinuousLinearMap.map_sub]
      abel
    rw [h_eq] at hsub
    exact hsub
  have h0_deriv : ∀ t ∈ Set.Ioo a b', HasDerivAt (fun _ : ℝ => (0 : G)) (A t ((fun _ => 0) t))
    t := by
    intro t _
    have h0 : HasDerivAt (fun _ : ℝ => (0 : G)) 0 t := hasDerivAt_const _ _
    have h_eq : (A t ((fun _ : ℝ => (0 : G)) t)) = 0 := by
      change A t 0 = 0
      rw [ContinuousLinearMap.map_zero]
    rw [h_eq]
    exact h0
  have hD_init : D h₀ = (fun _ : ℝ => (0 : G)) h₀ := by
    change Z₁ h₀ - Z₂ h₀ = 0
    rw [heq, sub_self]
  have hD_eq_zero : Set.EqOn D (fun _ : ℝ => (0 : G)) (Set.Ioo a b') :=
    linearODE_unique_on_Ioo ht₀ hA_cont hD_deriv h0_deriv hD_init
  intro t ht
  have h : D t = 0 := hD_eq_zero ht
  have h' : Z₁ t - Z₂ t = 0 := h
  exact sub_eq_zero.mp h'

theorem variationalW_add_in_v
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) (v₁ v₂ : F) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    variationalSolution A a b' h₀ Z₀ x (v₁ + v₂) t =
      variationalSolution A a b' h₀ Z₀ x v₁ t + variationalSolution A a b' h₀ Z₀ x v₂ t := by
  set Z₁ : ℝ → G := fun s => variationalSolution A a b' h₀ Z₀ x (v₁ + v₂) s with hZ₁_def
  set Z₂ : ℝ → G := fun s =>
    variationalSolution A a b' h₀ Z₀ x v₁ s + variationalSolution A a b' h₀ Z₀ x v₂ s with hZ₂_def
  set b : F → ℝ → G := fun y s => variationalForcing A a b' h₀ Z₀ y (v₁ + v₂) s with hb_def
  have hZ₁_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₁
      ((fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
          (linearODESolution A a b' h₀ Z₀ x s)
        + A x s (Z₁ s)) s := by
    intro s hs
    have := variationalW_hasDerivAt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx (v₁ + v₂) hs
    exact this
  have hZ₂_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₂
      ((fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
          (linearODESolution A a b' h₀ Z₀ x s)
        + A x s (Z₂ s)) s := by
    intro s hs
    have h1 := variationalW_hasDerivAt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx v₁ hs
    have h2 := variationalW_hasDerivAt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx v₂ hs
    have hsum := h1.add h2
    have h_eq :
        (fderiv ℝ (fun y => A y s) x) v₁ (linearODESolution A a b' h₀ Z₀ x s)
            + A x s (variationalSolution A a b' h₀ Z₀ x v₁ s)
          + ((fderiv ℝ (fun y => A y s) x) v₂ (linearODESolution A a b' h₀ Z₀ x s)
            + A x s (variationalSolution A a b' h₀ Z₀ x v₂ s))
        = (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₂ s) := by
      have hfderiv_add :
          (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            = (fderiv ℝ (fun y => A y s) x) v₁ + (fderiv ℝ (fun y => A y s) x) v₂ :=
        ContinuousLinearMap.map_add _ _ _
      rw [hfderiv_add]
      change
        (fderiv ℝ (fun y => A y s) x) v₁ (linearODESolution A a b' h₀ Z₀ x s)
            + A x s (variationalSolution A a b' h₀ Z₀ x v₁ s)
          + ((fderiv ℝ (fun y => A y s) x) v₂ (linearODESolution A a b' h₀ Z₀ x s)
            + A x s (variationalSolution A a b' h₀ Z₀ x v₂ s))
        = ((fderiv ℝ (fun y => A y s) x) v₁ + (fderiv ℝ (fun y => A y s) x) v₂)
              (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (variationalSolution A a b' h₀ Z₀ x v₁ s
              + variationalSolution A a b' h₀ Z₀ x v₂ s)
      rw [add_apply, ContinuousLinearMap.map_add]
      abel
    rw [← h_eq]
    exact hsum
  set Ax : ℝ → (G →L[ℝ] G) := fun s => A x s with hAx_def
  have hAx_cont : ContinuousOn Ax (Set.Ioo a b') := by
    intro s hs
    have h : ContinuousAt (fun p : F × ℝ => A p.1 p.2) (x, s) := by
      have : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hs⟩
      have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
      exact (hA_cont.continuousAt (hopen.mem_nhds this))
    have hAx_at : ContinuousAt Ax s := by
      have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
        Continuous.continuousAt (by continuity)
      exact h.comp hcurve
    exact hAx_at.continuousWithinAt
  set bs : ℝ → G := fun s =>
    (fderiv ℝ (fun y => A y s) x) (v₁ + v₂) (linearODESolution A a b' h₀ Z₀ x s)
    with hbs_def
  have hZ₁_deriv' : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₁ (Ax s (Z₁ s) + bs s) s := by
    intro s hs
    have h := hZ₁_deriv s hs
    have h_eq :
        (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₁ s)
        = Ax s (Z₁ s) + bs s := by
      change
        (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₁ s)
        = A x s (Z₁ s)
          + (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
              (linearODESolution A a b' h₀ Z₀ x s)
      abel
    rw [h_eq] at h
    exact h
  have hZ₂_deriv' : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₂ (Ax s (Z₂ s) + bs s) s := by
    intro s hs
    have h := hZ₂_deriv s hs
    have h_eq :
        (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₂ s)
        = Ax s (Z₂ s) + bs s := by
      change
        (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₂ s)
        = A x s (Z₂ s)
          + (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
              (linearODESolution A a b' h₀ Z₀ x s)
      abel
    rw [h_eq] at h
    exact h
  have hZ₁_init : Z₁ h₀ = (fderiv ℝ Z₀ x) (v₁ + v₂) :=
    variationalW_init A a b' h₀ Z₀ x (v₁ + v₂)
  have hZ₂_init : Z₂ h₀ = (fderiv ℝ Z₀ x) v₁ + (fderiv ℝ Z₀ x) v₂ := by
    change variationalSolution A a b' h₀ Z₀ x v₁ h₀ + variationalSolution A a b' h₀ Z₀ x v₂ h₀
      = (fderiv ℝ Z₀ x) v₁ + (fderiv ℝ Z₀ x) v₂
    rw [variationalW_init, variationalW_init]
  have hinit_eq : Z₁ h₀ = Z₂ h₀ := by
    rw [hZ₁_init, hZ₂_init, ContinuousLinearMap.map_add]
  have heq := inhomogLinearODE_unique_on_Ioo h₀_mem hAx_cont hZ₁_deriv' hZ₂_deriv' hinit_eq
  exact heq ht

theorem variationalW_smul_in_v
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) (c : ℝ) (v : F) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    variationalSolution A a b' h₀ Z₀ x (c • v) t = c • variationalSolution A a b' h₀ Z₀ x v t := by
  set Z₁ : ℝ → G := fun s => variationalSolution A a b' h₀ Z₀ x (c • v) s with hZ₁_def
  set Z₂ : ℝ → G := fun s => c • variationalSolution A a b' h₀ Z₀ x v s with hZ₂_def
  set Ax : ℝ → (G →L[ℝ] G) := fun s => A x s with hAx_def
  have hAx_cont : ContinuousOn Ax (Set.Ioo a b') := by
    intro s hs
    have h : ContinuousAt (fun p : F × ℝ => A p.1 p.2) (x, s) := by
      have : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hs⟩
      have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
      exact (hA_cont.continuousAt (hopen.mem_nhds this))
    have hAx_at : ContinuousAt Ax s := by
      have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
        Continuous.continuousAt (by continuity)
      exact h.comp hcurve
    exact hAx_at.continuousWithinAt
  set bs : ℝ → G := fun s =>
    (fderiv ℝ (fun y => A y s) x) (c • v) (linearODESolution A a b' h₀ Z₀ x s)
    with hbs_def
  have hZ₁_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₁ (Ax s (Z₁ s) + bs s) s := by
    intro s hs
    have h := variationalW_hasDerivAt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx (c • v) hs
    have h_eq :
        (fderiv ℝ (fun y => A y s) x) (c • v)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₁ s)
        = Ax s (Z₁ s) + bs s := by
      change
        (fderiv ℝ (fun y => A y s) x) (c • v)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₁ s)
        = A x s (Z₁ s)
          + (fderiv ℝ (fun y => A y s) x) (c • v)
              (linearODESolution A a b' h₀ Z₀ x s)
      abel
    rw [h_eq] at h
    exact h
  have hZ₂_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₂ (Ax s (Z₂ s) + bs s) s := by
    intro s hs
    have h := variationalW_hasDerivAt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx v hs
    have hsmul : HasDerivAt (fun s' => c • variationalSolution A a b' h₀ Z₀ x v s')
        (c • ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (variationalSolution A a b' h₀ Z₀ x v s))) s := h.const_smul c
    have h_eq :
        c • ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
              + A x s (variationalSolution A a b' h₀ Z₀ x v s))
        = Ax s (Z₂ s) + bs s := by
      have hL :
          (fderiv ℝ (fun y => A y s) x) (c • v)
            = c • (fderiv ℝ (fun y => A y s) x) v :=
        ContinuousLinearMap.map_smul _ _ _
      change
        c • ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
              + A x s (variationalSolution A a b' h₀ Z₀ x v s))
        = A x s (c • variationalSolution A a b' h₀ Z₀ x v s)
          + (fderiv ℝ (fun y => A y s) x) (c • v)
              (linearODESolution A a b' h₀ Z₀ x s)
      rw [hL, smul_apply, ContinuousLinearMap.map_smul, smul_add]
      abel
    rw [← h_eq]
    exact hsmul
  have hZ₁_init : Z₁ h₀ = (fderiv ℝ Z₀ x) (c • v) :=
    variationalW_init A a b' h₀ Z₀ x (c • v)
  have hZ₂_init : Z₂ h₀ = c • (fderiv ℝ Z₀ x) v := by
    change c • variationalSolution A a b' h₀ Z₀ x v h₀ = c • (fderiv ℝ Z₀ x) v
    rw [variationalW_init]
  have hinit_eq : Z₁ h₀ = Z₂ h₀ := by
    rw [hZ₁_init, hZ₂_init, ContinuousLinearMap.map_smul]
  have heq := inhomogLinearODE_unique_on_Ioo h₀_mem hAx_cont hZ₁_deriv hZ₂_deriv hinit_eq
  exact heq ht

theorem variationalW_linear_in_v
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    (∀ v₁ v₂ : F, variationalSolution A a b' h₀ Z₀ x (v₁ + v₂) t =
        variationalSolution A a b' h₀ Z₀ x v₁ t + variationalSolution A a b' h₀ Z₀ x v₂ t) ∧
    (∀ (c : ℝ) (v : F), variationalSolution A a b' h₀ Z₀ x (c • v) t =
        c • variationalSolution A a b' h₀ Z₀ x v t) :=
  ⟨fun v₁ v₂ => variationalW_add_in_v h₀_mem hU hA_cont hDA_cont hZ₀_cont hx v₁ v₂ ht,
   fun c v => variationalW_smul_in_v h₀_mem hU hA_cont hDA_cont hZ₀_cont hx c v ht⟩

private theorem variationalW_norm_bound_on_Icc
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U)
    {α β : ℝ} (_hαβ : α ≤ β) (hα_lt : a < α) (hβ_lt : β < b')
    (hh₀_mem : h₀ ∈ Set.Icc α β)
    (M P Q R : ℝ) (hM_nn : 0 ≤ M) (hP_nn : 0 ≤ P) (hQ_nn : 0 ≤ Q) (hR_nn : 0 ≤ R)
    (hA_bd : ∀ s ∈ Set.Icc α β, ‖A x s‖ ≤ M)
    (hDA_bd : ∀ s ∈ Set.Icc α β, ‖fderiv ℝ (fun y => A y s) x‖ ≤ P)
    (hZ_bd : ∀ s ∈ Set.Icc α β, ‖linearODESolution A a b' h₀ Z₀ x s‖ ≤ Q)
    (hZ₀'_bd : ‖fderiv ℝ Z₀ x‖ ≤ R)
    (v : F) (t : ℝ) (ht : t ∈ Set.Icc α β) :
    ‖variationalSolution A a b' h₀ Z₀ x v t‖
      ≤ gronwallBound R M (P * Q) (β - α) * ‖v‖ := by
  set W : ℝ → G := variationalSolution A a b' h₀ Z₀ x v with hW_def
  have hsub_open : Set.Icc α β ⊆ Set.Ioo a b' := fun s hs =>
    ⟨lt_of_lt_of_le hα_lt hs.1, lt_of_le_of_lt hs.2 hβ_lt⟩
  have hW_deriv : ∀ s ∈ Set.Icc α β,
      HasDerivAt W
        ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (W s)) s := fun s hs =>
    variationalW_hasDerivAt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx v (hsub_open hs)
  have hW_cont : ContinuousOn W (Set.Icc α β) := fun s hs =>
    ((hW_deriv s hs).continuousAt).continuousWithinAt
  have hW_init : W h₀ = (fderiv ℝ Z₀ x) v := variationalW_init A a b' h₀ Z₀ x v
  set bv : ℝ → G := fun s =>
    (fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s) with hbv_def
  have hbv_bd : ∀ s ∈ Set.Icc α β, ‖bv s‖ ≤ P * Q * ‖v‖ := by
    intro s hs
    have h1 : ‖(fderiv ℝ (fun y => A y s) x) v‖
        ≤ ‖fderiv ℝ (fun y => A y s) x‖ * ‖v‖ :=
      (fderiv ℝ (fun y => A y s) x).le_opNorm v
    have h2 : ‖(fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)‖
        ≤ ‖(fderiv ℝ (fun y => A y s) x) v‖ * ‖linearODESolution A a b' h₀ Z₀ x s‖ :=
      ((fderiv ℝ (fun y => A y s) x) v).le_opNorm _
    have h3 : ‖(fderiv ℝ (fun y => A y s) x) v‖ * ‖linearODESolution A a b' h₀ Z₀ x s‖
        ≤ (‖fderiv ℝ (fun y => A y s) x‖ * ‖v‖)
            * ‖linearODESolution A a b' h₀ Z₀ x s‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h4 : (‖fderiv ℝ (fun y => A y s) x‖ * ‖v‖)
            * ‖linearODESolution A a b' h₀ Z₀ x s‖
        ≤ (P * ‖v‖) * Q :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hDA_bd s hs) (norm_nonneg _))
        (hZ_bd s hs) (norm_nonneg _) (by positivity)
    calc ‖bv s‖ ≤ ‖(fderiv ℝ (fun y => A y s) x) v‖
                  * ‖linearODESolution A a b' h₀ Z₀ x s‖ := h2
      _ ≤ (‖fderiv ℝ (fun y => A y s) x‖ * ‖v‖)
            * ‖linearODESolution A a b' h₀ Z₀ x s‖ := h3
      _ ≤ (P * ‖v‖) * Q := h4
      _ = P * Q * ‖v‖ := by ring
  have h_h₀_le_β : h₀ ≤ β := hh₀_mem.2
  have h_α_le_h₀ : α ≤ h₀ := hh₀_mem.1
  have hIcc_fwd_sub : Set.Icc h₀ β ⊆ Set.Icc α β := fun s hs =>
    ⟨le_trans h_α_le_h₀ hs.1, hs.2⟩
  have hIcc_bwd_sub : Set.Icc α h₀ ⊆ Set.Icc α β := fun s hs =>
    ⟨hs.1, le_trans hs.2 h_h₀_le_β⟩
  have hW'_bound : ∀ s ∈ Set.Icc α β,
      ‖(fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
        + A x s (W s)‖ ≤ M * ‖W s‖ + P * Q * ‖v‖ := by
    intro s hs
    have ha : ‖A x s (W s)‖ ≤ M * ‖W s‖ := by
      have h1 : ‖A x s (W s)‖ ≤ ‖A x s‖ * ‖W s‖ := (A x s).le_opNorm (W s)
      have h2 : ‖A x s‖ * ‖W s‖ ≤ M * ‖W s‖ :=
        mul_le_mul_of_nonneg_right (hA_bd s hs) (norm_nonneg _)
      linarith
    have hb : ‖bv s‖ ≤ P * Q * ‖v‖ := hbv_bd s hs
    have h_tri := norm_add_le (bv s) (A x s (W s))
    calc ‖bv s + A x s (W s)‖
        ≤ ‖bv s‖ + ‖A x s (W s)‖ := h_tri
      _ ≤ P * Q * ‖v‖ + M * ‖W s‖ := by linarith
      _ = M * ‖W s‖ + P * Q * ‖v‖ := by ring
  have hW_init_bd : ‖W h₀‖ ≤ R * ‖v‖ := by
    rw [hW_init]
    calc ‖(fderiv ℝ Z₀ x) v‖
        ≤ ‖fderiv ℝ Z₀ x‖ * ‖v‖ := (fderiv ℝ Z₀ x).le_opNorm v
      _ ≤ R * ‖v‖ := mul_le_mul_of_nonneg_right hZ₀'_bd (norm_nonneg _)
  have hv_nn : 0 ≤ ‖v‖ := norm_nonneg _
  have hPQ_nn : 0 ≤ P * Q := mul_nonneg hP_nn hQ_nn
  have h_gb_scale : ∀ y : ℝ,
      gronwallBound (R * ‖v‖) M (P * Q * ‖v‖) y
        = gronwallBound R M (P * Q) y * ‖v‖ := by
    intro y
    by_cases hM_eq : M = 0
    · simp only [gronwallBound_K0, hM_eq]
      ring
    · simp only [gronwallBound_of_K_ne_0 hM_eq]
      field_simp
  have h_gb_mono : ∀ y₁ y₂ : ℝ, y₁ ≤ y₂ →
      gronwallBound R M (P * Q) y₁ ≤ gronwallBound R M (P * Q) y₂ :=
    fun y₁ y₂ hy => gronwallBound_mono hR_nn hPQ_nn hM_nn hy
  rcases le_total h₀ t with hh₀t | hth₀
  · have ht' : t ∈ Set.Icc h₀ β := ⟨hh₀t, ht.2⟩
    have hW_cont_fwd : ContinuousOn W (Set.Icc h₀ β) := hW_cont.mono hIcc_fwd_sub
    have hW_deriv_right : ∀ s ∈ Set.Ico h₀ β, HasDerivWithinAt W
        ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (W s)) (Set.Ici s) s := fun s hs =>
      (hW_deriv s (hIcc_fwd_sub (Set.Ico_subset_Icc_self hs))).hasDerivWithinAt
    have hbound_fwd : ∀ s ∈ Set.Ico h₀ β,
        ‖(fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (W s)‖ ≤ M * ‖W s‖ + P * Q * ‖v‖ := fun s hs =>
      hW'_bound s (hIcc_fwd_sub (Set.Ico_subset_Icc_self hs))
    have hgw := norm_le_gronwallBound_of_norm_deriv_right_le
      hW_cont_fwd hW_deriv_right hW_init_bd hbound_fwd t ht'
    rw [h_gb_scale (t - h₀)] at hgw
    have h_t_sub_le : t - h₀ ≤ β - α := by linarith [ht.2, h_α_le_h₀]
    have h_step : gronwallBound R M (P * Q) (t - h₀) ≤ gronwallBound R M (P * Q) (β - α) :=
      h_gb_mono _ _ h_t_sub_le
    calc ‖W t‖
        ≤ gronwallBound R M (P * Q) (t - h₀) * ‖v‖ := hgw
      _ ≤ gronwallBound R M (P * Q) (β - α) * ‖v‖ :=
          mul_le_mul_of_nonneg_right h_step hv_nn
  · have ht' : t ∈ Set.Icc α h₀ := ⟨ht.1, hth₀⟩
    set Wb : ℝ → G := fun s => W (2 * h₀ - s) with hWb_def
    have h_h₀_le_2h₀mt : h₀ ≤ 2 * h₀ - t := by linarith
    have h_dom_swap : ∀ s ∈ Set.Icc h₀ (2 * h₀ - t), 2 * h₀ - s ∈ Set.Icc α h₀ := by
      intro s hs
      refine ⟨?_, ?_⟩
      · linarith [hs.2, ht'.1]
      · linarith [hs.1]
    have hWb_cont : ContinuousOn Wb (Set.Icc h₀ (2 * h₀ - t)) := by
      apply ContinuousOn.comp (hW_cont.mono hIcc_bwd_sub) (s := Set.Icc h₀ (2 * h₀ - t))
        (t := Set.Icc α h₀) (f := fun s => 2 * h₀ - s)
      · exact (continuous_const.sub continuous_id).continuousOn
      · exact h_dom_swap
    have hWb_deriv : ∀ s ∈ Set.Icc h₀ (2 * h₀ - t),
        HasDerivAt Wb (-((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s)))) s := by
      intro s hs
      have hd : HasDerivAt W
          ((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
            (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
          + A x (2 * h₀ - s) (W (2 * h₀ - s))) (2 * h₀ - s) :=
        hW_deriv (2 * h₀ - s) (hIcc_bwd_sub (h_dom_swap s hs))
      have h_chain : HasDerivAt (fun r : ℝ => 2 * h₀ - r) (-1 : ℝ) s := by
        refine (((hasDerivAt_const s (2 * h₀)).sub (hasDerivAt_id s)).congr_of_eventuallyEq
          ?_).congr_deriv ?_
        · exact Filter.Eventually.of_forall fun r => by
            change 2 * h₀ - r = 2 * h₀ - r
            rfl
        · norm_num
      have hd' := hd.scomp s h_chain
      have h_eq_smul :
          (-1 : ℝ) • ((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s)))
          = -((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s))) :=
        neg_one_smul ℝ _
      rw [h_eq_smul] at hd'
      exact hd'
    have hWb_init : Wb h₀ = W h₀ := by
      change W (2 * h₀ - h₀) = W h₀
      have : 2 * h₀ - h₀ = h₀ := by ring
      rw [this]
    have hWb'_bound : ∀ s ∈ Set.Icc h₀ (2 * h₀ - t),
        ‖-((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s)))‖
          ≤ M * ‖Wb s‖ + P * Q * ‖v‖ := by
      intro s hs
      have h_in : 2 * h₀ - s ∈ Set.Icc α β := hIcc_bwd_sub (h_dom_swap s hs)
      have h := hW'_bound (2 * h₀ - s) h_in
      have hWbs_eq : Wb s = W (2 * h₀ - s) := rfl
      rw [norm_neg, hWbs_eq]
      exact h
    have hWb_init_bd : ‖Wb h₀‖ ≤ R * ‖v‖ := by
      rw [hWb_init]; exact hW_init_bd
    have hWb_deriv_right : ∀ s ∈ Set.Ico h₀ (2 * h₀ - t),
        HasDerivWithinAt Wb (-((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
            (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
          + A x (2 * h₀ - s) (W (2 * h₀ - s)))) (Set.Ici s) s := fun s hs =>
      (hWb_deriv s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt
    have hbound_bwd : ∀ s ∈ Set.Ico h₀ (2 * h₀ - t),
        ‖-((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s)))‖
          ≤ M * ‖Wb s‖ + P * Q * ‖v‖ := fun s hs =>
      hWb'_bound s (Set.Ico_subset_Icc_self hs)
    have hgw_bwd := norm_le_gronwallBound_of_norm_deriv_right_le
      hWb_cont hWb_deriv_right hWb_init_bd hbound_bwd
      (2 * h₀ - t) (right_mem_Icc.mpr h_h₀_le_2h₀mt)
    have hWb_t : Wb (2 * h₀ - t) = W t := by
      change W (2 * h₀ - (2 * h₀ - t)) = W t
      have : 2 * h₀ - (2 * h₀ - t) = t := by ring
      rw [this]
    rw [hWb_t] at hgw_bwd
    have h_time : 2 * h₀ - t - h₀ = h₀ - t := by ring
    rw [h_time] at hgw_bwd
    rw [h_gb_scale (h₀ - t)] at hgw_bwd
    have h_h₀mt_le : h₀ - t ≤ β - α := by linarith [ht.1, h_h₀_le_β]
    have h_step : gronwallBound R M (P * Q) (h₀ - t) ≤ gronwallBound R M (P * Q) (β - α) :=
      h_gb_mono _ _ h_h₀mt_le
    calc ‖W t‖
        ≤ gronwallBound R M (P * Q) (h₀ - t) * ‖v‖ := hgw_bwd
      _ ≤ gronwallBound R M (P * Q) (β - α) * ‖v‖ :=
          mul_le_mul_of_nonneg_right h_step hv_nn

noncomputable def variationalWClm
    {A : F → ℝ → (G →L[ℝ] G)} {a b' : ℝ}
    {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {Z₀ : F → G}
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    F →L[ℝ] G :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun v => variationalSolution A a b' h₀ Z₀ x v t
      map_add' := fun v₁ v₂ =>
        variationalW_add_in_v h₀_mem hU hA_cont hDA_cont hZ₀_cont hx v₁ v₂ ht
      map_smul' := fun c v => by
        have h := variationalW_smul_in_v h₀_mem hU hA_cont hDA_cont hZ₀_cont
          hx c v ht
        simpa using h }
    (by
      classical
      set α := (a + min t h₀) / 2 with hα_def
      set β := (b' + max t h₀) / 2 with hβ_def
      have hmin_lt : a < min t h₀ := lt_min ht.1 h₀_mem.1
      have hmax_lt : max t h₀ < b' := max_lt ht.2 h₀_mem.2
      have hmin_le_t : min t h₀ ≤ t := min_le_left _ _
      have hmin_le_t₀ : min t h₀ ≤ h₀ := min_le_right _ _
      have ht_le_max : t ≤ max t h₀ := le_max_left _ _
      have ht₀_le_max : h₀ ≤ max t h₀ := le_max_right _ _
      have hα_lt_min : α < min t h₀ := by rw [hα_def]; linarith
      have ha_lt_α : a < α := by rw [hα_def]; linarith
      have hmax_lt_β : max t h₀ < β := by rw [hβ_def]; linarith
      have hβ_lt_b' : β < b' := by rw [hβ_def]; linarith
      have hα_le_β : α ≤ β := by linarith
      have hh₀_mem : h₀ ∈ Set.Icc α β :=
        ⟨le_of_lt (lt_of_lt_of_le hα_lt_min hmin_le_t₀),
         le_of_lt (lt_of_le_of_lt ht₀_le_max hmax_lt_β)⟩
      have h_t_Icc : t ∈ Set.Icc α β :=
        ⟨le_of_lt (lt_of_lt_of_le hα_lt_min hmin_le_t),
         le_of_lt (lt_of_le_of_lt ht_le_max hmax_lt_β)⟩
      have hIcc_sub : Set.Icc α β ⊆ Set.Ioo a b' := fun s hs =>
        ⟨lt_of_lt_of_le ha_lt_α hs.1, lt_of_le_of_lt hs.2 hβ_lt_b'⟩
      have hIcc_cpt : IsCompact (Set.Icc α β) := isCompact_Icc
      have hIcc_ne : (Set.Icc α β).Nonempty := ⟨α, left_mem_Icc.mpr hα_le_β⟩
      have hAx_cont_Icc : ContinuousOn (fun s => A x s) (Set.Icc α β) := by
        intro s hs
        have h : ContinuousAt (fun p : F × ℝ => A p.1 p.2) (x, s) := by
          have hxs : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hIcc_sub hs⟩
          have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
          exact hA_cont.continuousAt (hopen.mem_nhds hxs)
        have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
          Continuous.continuousAt (by continuity)
        exact (h.comp hcurve).continuousWithinAt
      have h_normA_cont : ContinuousOn (fun s => ‖A x s‖) (Set.Icc α β) :=
        continuous_norm.comp_continuousOn hAx_cont_Icc
      obtain ⟨σM, _, hM_bd⟩ := hIcc_cpt.exists_isMaxOn hIcc_ne h_normA_cont
      let Mv : ℝ := ‖A x σM‖
      have hMv_nn : 0 ≤ Mv := norm_nonneg _
      have hMv_bd : ∀ s ∈ Set.Icc α β, ‖A x s‖ ≤ Mv := fun s hs => hM_bd hs
      have hDAx_cont_Icc : ContinuousOn (fun s => fderiv ℝ (fun y => A y s) x)
          (Set.Icc α β) := by
        intro s hs
        have h : ContinuousAt (Function.uncurry fun x' t' => fderiv ℝ (fun y => A y t') x')
            (x, s) := by
          have hxs : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hIcc_sub hs⟩
          have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
          exact hDA_cont.continuousAt (hopen.mem_nhds hxs)
        have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
          Continuous.continuousAt (by continuity)
        exact (h.comp hcurve).continuousWithinAt
      have h_normDA_cont : ContinuousOn (fun s => ‖fderiv ℝ (fun y => A y s) x‖)
          (Set.Icc α β) := by
        simpa only using hDAx_cont_Icc.norm
      obtain ⟨σP, _, hP_bd⟩ := hIcc_cpt.exists_isMaxOn hIcc_ne h_normDA_cont
      let Pv : ℝ := ‖fderiv ℝ (fun y => A y σP) x‖
      have hPv_nn : 0 ≤ Pv := norm_nonneg _
      have hPv_bd : ∀ s ∈ Set.Icc α β, ‖fderiv ℝ (fun y => A y s) x‖ ≤ Pv :=
        fun s hs => hP_bd hs
      have hZ_cont_full : ContinuousOn (Function.uncurry (linearODESolution A a b' h₀ Z₀))
          (U ×ˢ Set.Ioo a b') :=
        linearODESolution_continuousOn h₀_mem hU hA_cont hZ₀_cont
      have hZx_cont_Icc : ContinuousOn (linearODESolution A a b' h₀ Z₀ x) (Set.Icc α β) := by
        intro s hs
        have h : ContinuousAt (Function.uncurry (linearODESolution A a b' h₀ Z₀)) (x, s) := by
          have hxs : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hIcc_sub hs⟩
          have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
          exact hZ_cont_full.continuousAt (hopen.mem_nhds hxs)
        have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
          Continuous.continuousAt (by continuity)
        exact (h.comp hcurve).continuousWithinAt
      have h_normZ_cont : ContinuousOn (fun s => ‖linearODESolution A a b' h₀ Z₀ x s‖)
          (Set.Icc α β) := continuous_norm.comp_continuousOn hZx_cont_Icc
      obtain ⟨σQ, _, hQ_bd⟩ := hIcc_cpt.exists_isMaxOn hIcc_ne h_normZ_cont
      let Qv : ℝ := ‖linearODESolution A a b' h₀ Z₀ x σQ‖
      have hQv_nn : 0 ≤ Qv := norm_nonneg _
      have hQv_bd : ∀ s ∈ Set.Icc α β, ‖linearODESolution A a b' h₀ Z₀ x s‖ ≤ Qv :=
        fun s hs => hQ_bd hs
      let Rv : ℝ := ‖fderiv ℝ Z₀ x‖
      have hRv_nn : 0 ≤ Rv := norm_nonneg _
      refine ⟨gronwallBound Rv Mv (Pv * Qv) (β - α), fun v => ?_⟩
      have h := variationalW_norm_bound_on_Icc h₀_mem hU hA_cont hDA_cont hZ₀_cont
        hx hα_le_β ha_lt_α hβ_lt_b' hh₀_mem Mv Pv Qv Rv hMv_nn hPv_nn hQv_nn hRv_nn
        hMv_bd hPv_bd hQv_bd le_rfl v t h_t_Icc
      simpa using h)

@[simp]
theorem variationalW_clm_apply
    {A : F → ℝ → (G →L[ℝ] G)} {a b' : ℝ}
    {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {Z₀ : F → G}
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') (v : F) :
    variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht v
      = variationalSolution A a b' h₀ Z₀ x v t := rfl

end VariationalSolution

end Poincare.ODE.LocalFlow

end
