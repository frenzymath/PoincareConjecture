import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Analysis.Jets.UniformCompactDerivative

/-!
# Compact convergence of arbitrary finite jets under composition

The induction applies the differentiated chain rule to the compact
value-and-derivative image. It uses actual neighborhood identities at
every stage, so totalized derivatives outside the smooth domains do
not enter the proof. This supplies the higher variational fields for
Morgan--Tian, Claim 16.6, pp. 371-372; see derivation 22.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

universe u

/-- Zeroth-jet convergence is ordinary uniform convergence. -/
theorem tendstoUniformlyOn_of_iteratedFDeriv_zero
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {l : Filter ι}
    {fseq : ι → E → F} {f : E → F} {K : Set E}
    (h : TendstoUniformlyOn (fun i => iteratedFDeriv ℝ 0 (fseq i))
      (iteratedFDeriv ℝ 0 f) l K) : TendstoUniformlyOn fseq f l K := by
  simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
    (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → E)).comp_tendstoUniformlyOn h

/-- The right currying isometry reconstructs the next jet from the
converging jets of the actual continuous linear derivative. -/
theorem tendstoUniformlyOn_iteratedFDeriv_succ_of_fderiv
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {l : Filter ι}
    {fseq : ι → E → F} {f : E → F} {K : Set E} {j : ℕ}
    (h : TendstoUniformlyOn (fun i => iteratedFDeriv ℝ j (fderiv ℝ (fseq i)))
      (iteratedFDeriv ℝ j (fderiv ℝ f)) l K) :
    TendstoUniformlyOn (fun i => iteratedFDeriv ℝ (j + 1) (fseq i))
      (iteratedFDeriv ℝ (j + 1) f) l K := by
  have hc := (continuousMultilinearCurryRightEquiv' ℝ j E F).symm.isometry.uniformContinuous
  have hconv := hc.comp_tendstoUniformlyOn h
  have he (g : E → F) : iteratedFDeriv ℝ (j + 1) g =
      (continuousMultilinearCurryRightEquiv' ℝ j E F).symm ∘
        iteratedFDeriv ℝ j (fderiv ℝ g) :=
    funext fun _ => iteratedFDeriv_succ_eq_comp_right
  simpa only [he] using hconv

/-- Pairing actual smooth maps preserves uniform convergence of each
fixed finite jet on the same parameter set. -/
theorem tendstoUniformlyOn_iteratedFDeriv_prodMk
    {E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {l : Filter ι}
    {fseq : ι → E → F} {f : E → F} {gseq : ι → E → G} {g : E → G} {K : Set E} (j : ℕ)
    (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) (hg : ∀ x ∈ K, ContDiffAt ℝ ∞ g x)
    (hfs : ∀ᶠ i in l, ∀ x ∈ K, ContDiffAt ℝ ∞ (fseq i) x)
    (hgs : ∀ᶠ i in l, ∀ x ∈ K, ContDiffAt ℝ ∞ (gseq i) x)
    (hfjet : TendstoUniformlyOn (fun i => iteratedFDeriv ℝ j (fseq i))
      (iteratedFDeriv ℝ j f) l K)
    (hgjet : TendstoUniformlyOn (fun i => iteratedFDeriv ℝ j (gseq i))
      (iteratedFDeriv ℝ j g) l K) :
    TendstoUniformlyOn (fun i => iteratedFDeriv ℝ j (fun x => (fseq i x, gseq i x)))
      (iteratedFDeriv ℝ j (fun x => (f x, g x))) l K := by
  have hprod := (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin j => E) F G).isometry
  have hconv := hprod.uniformContinuous.comp_tendstoUniformlyOn (hfjet.prodMk_same hgjet)
  apply (hconv.congr ?_).congr_right ?_
  · filter_upwards [hfs, hgs] with i hfi hgi
    intro x hx
    exact (iteratedFDeriv_prodMk (hfi x hx) (hgi x hx) (by exact_mod_cast le_top)).symm
  · intro x hx
    exact (iteratedFDeriv_prodMk (hf x hx) (hg x hx) (by exact_mod_cast le_top)).symm

private theorem fderiv_comp_germ
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x)) :
    fderiv ℝ (g ∘ f) =ᶠ[𝓝 x] fun y => (fderiv ℝ g (f y)).comp (fderiv ℝ f y) := by
  have hfn := (hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by decide)
  have hgn := (hg.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by decide)
  filter_upwards [hfn, hf.continuousAt.eventually hgn] with y hy hyg
  exact fderiv_comp y (hyg.differentiableAt one_ne_zero) (hy.differentiableAt one_ne_zero)

/-- Every finite derivative of a composition converges uniformly when
the inner jets converge on a compact set and the fixed outer map is
smooth on an open neighborhood of the limiting image. -/
theorem tendstoUniformlyOn_iteratedFDeriv_comp_of_compact
    (m : ℕ) {E F G : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ι : Type*} {l : Filter ι} {fseq : ι → E → F} {f : E → F} {g : F → G}
    {K : Set E} {U : Set F} (hK : IsCompact K) (hU : IsOpen U)
    (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) (hg : ContDiffOn ℝ ∞ g U)
    (hfU : MapsTo f K U)
    (hfs : ∀ᶠ i in l, ∀ x ∈ K, ContDiffAt ℝ ∞ (fseq i) x)
    (hjet : ∀ j ≤ m, TendstoUniformlyOn (fun i => iteratedFDeriv ℝ j (fseq i))
      (iteratedFDeriv ℝ j f) l K) :
    TendstoUniformlyOn (fun i => iteratedFDeriv ℝ m (g ∘ fseq i))
      (iteratedFDeriv ℝ m (g ∘ f)) l K := by
  induction m generalizing F G with
  | zero =>
    have hzero := tendstoUniformlyOn_of_iteratedFDeriv_zero (hjet 0 le_rfl)
    have hvalue := hg.continuousOn.comp_tendstoUniformlyOn_of_compact_image hU
      (hK.image_of_continuousOn (fun x hx => (hf x hx).continuousAt.continuousWithinAt)) hfU hzero
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E G).symm.isometry.uniformContinuous.comp_tendstoUniformlyOn
        hvalue
  | succ m ih =>
    let J (h : E → F) (x : E) : F × (E →L[ℝ] F) := (h x, fderiv ℝ h x)
    let H (z : F × (E →L[ℝ] F)) : E →L[ℝ] G := (fderiv ℝ g z.1).comp z.2
    have hJ : ∀ x ∈ K, ContDiffAt ℝ ∞ (J f) x := fun x hx =>
      (hf x hx).prodMk ((hf x hx).fderiv_right (m := ∞) (by simp))
    have hJs : ∀ᶠ i in l, ∀ x ∈ K, ContDiffAt ℝ ∞ (J (fseq i)) x := by
      filter_upwards [hfs] with i hi
      exact fun x hx => (hi x hx).prodMk ((hi x hx).fderiv_right (m := ∞) (by simp))
    have hH : ContDiffOn ℝ ∞ H (U ×ˢ univ) := by
      intro z hz
      exact ((((hg.contDiffAt (hU.mem_nhds hz.1)).fderiv_right (m := ∞) (by simp)).comp
        z contDiffAt_fst).clm_comp contDiffAt_snd).contDiffWithinAt
    have hJjet : ∀ j ≤ m, TendstoUniformlyOn (fun i => iteratedFDeriv ℝ j (J (fseq i)))
        (iteratedFDeriv ℝ j (J f)) l K := by
      intro j hj
      apply tendstoUniformlyOn_iteratedFDeriv_prodMk j hf
        (fun x hx => (hf x hx).fderiv_right (m := ∞) (by simp)) hfs
        (hfs.mono fun i hi x hx => (hi x hx).fderiv_right (m := ∞) (by simp))
        (hjet j (hj.trans (Nat.le_succ m)))
      exact tendstoUniformlyOn_iteratedFDeriv_fderiv
        (hjet (j + 1) (Nat.add_le_add_right hj 1))
    have hconv := ih (F := F × (E →L[ℝ] F)) (G := E →L[ℝ] G)
      (hU.prod isOpen_univ) hJ hH (fun x hx => ⟨hfU hx, mem_univ _⟩) hJs hJjet
    have hzero := tendstoUniformlyOn_of_iteratedFDeriv_zero (hjet 0 (Nat.zero_le _))
    have hfit := hzero.eventually_mapsTo_of_compact_image
      (hK.image_of_continuousOn (fun x hx => (hf x hx).continuousAt.continuousWithinAt)) hU hfU
    have hconvD : TendstoUniformlyOn (fun i => iteratedFDeriv ℝ m (fderiv ℝ (g ∘ fseq i)))
        (iteratedFDeriv ℝ m (fderiv ℝ (g ∘ f))) l K := by
      apply (hconv.congr ?_).congr_right ?_
      · filter_upwards [hfs, hfit] with i hi him
        intro x hx
        exact ((fderiv_comp_germ (hi x hx)
          (hg.contDiffAt (hU.mem_nhds (him hx)))).iteratedFDeriv ℝ m).self_of_nhds.symm
      · intro x hx
        exact ((fderiv_comp_germ (hf x hx)
          (hg.contDiffAt (hU.mem_nhds (hfU hx)))).iteratedFDeriv ℝ m).self_of_nhds.symm
    exact tendstoUniformlyOn_iteratedFDeriv_succ_of_fderiv hconvD
