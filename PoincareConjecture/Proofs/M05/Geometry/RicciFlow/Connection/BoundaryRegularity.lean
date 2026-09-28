import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Connection.Regularity
import PoincareConjecture.Definitions.Ch01.ScalarOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

lemma contMDiffWithinAt_inner_fields (F : RicciFlow n M J) {t : ℝ}
    (ht : t ∈ J) {x : M}
    {X Y : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.metric p.1).inner p.2 (X p.2) (Y p.2)) (J ×ˢ univ) (t, x) := by
  have hg := F.smooth (t, x) ⟨ht, mem_univ x⟩
  have hX' : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.2))
      (J ×ˢ univ) (t, x) := (hX.comp (t, x) contMDiffAt_snd).contMDiffWithinAt
  have hY' : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Y p.2))
      (J ×ˢ univ) (t, x) := (hY.comp (t, x) contMDiffAt_snd).contMDiffWithinAt
  have h := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : M => ℝ) hX' hY'
  exact (contMDiffWithinAt_totalSpace.mp h).2

private lemma contDiffWithinAt_mvfderiv_time
    {f : ℝ × M → ℝ} {t : ℝ} {x : M} (ht : t ∈ J)
    (hf : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (J ×ˢ univ) (t, x))
    (hspace : ∀ s, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => f (s, y)) x)
    (v : TangentSpace (𝓡 n) x) :
    ContDiffWithinAt ℝ ∞ (fun s => mvfderiv (𝓡 n) (fun y => f (s, y)) x v) J t := by
  let e := extChartAt (𝓡 n) x
  have hx : e.symm (e x) = x := e.left_inv (mem_extChartAt_source x)
  have hs : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ e.symm (e x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  have hc : ContDiffWithinAt ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => f (p.1, e.symm p.2))
      (J ×ˢ univ) (t, e x) := by
    have hp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, e.symm p.2)) (t, e x) :=
      contMDiffAt_fst.prodMk (hs.comp (t, e x) contMDiffAt_snd)
    have h := hf.comp_of_eq hp.contMDiffWithinAt
      (show MapsTo (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, e.symm p.2))
        (J ×ˢ univ) (J ×ˢ univ) from fun p hp => ⟨hp.1, mem_univ _⟩) (by simp [hx])
    simp +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffWithinAt
  have hd := hc.fderivWithin (f := fun s z => f (s, e.symm z))
    (g := fun _ : ℝ => e x) contDiffWithinAt_const uniqueDiffOn_univ
    (m := ∞) (by simp) ht (by simp)
  simp only [fderivWithin_univ] at hd
  let w : EuclideanSpace ℝ (Fin n) :=
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) e.symm (e x)).inverse v
  have hh := hd.clm_apply (contDiffWithinAt_const (c := w))
  apply hh.congr_of_eventuallyEq_insert
  apply Filter.Eventually.of_forall
  intro s
  have h := Poincare.Manifold.VectorField.fderiv_comp_extChartAt_symm
    (p := x) (by simpa [e, hx] using hspace s) (mem_extChartAt_target x) w
  have hi := Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm
    (I := 𝓡 n) (p := x) (mem_extChartAt_target x)
  change fderiv ℝ ((fun y => f (s, y)) ∘ e.symm) (e x) w =
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun y => f (s, y)) (e.symm (e x))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) e.symm (e x) w) at h
  dsimp only [w] at h
  rw [hi.self_apply_inverse, hx] at h
  exact h.symm

private lemma contDiffWithinAt_clm_of_apply
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ E]
    {f : ℝ → E →L[ℝ] G} {t : ℝ}
    (hf : ∀ v, ContDiffWithinAt ℝ ∞ (fun s => f s v) J t) :
    ContDiffWithinAt ℝ ∞ f J t := by
  let d := Module.finrank ℝ E
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ : E ≃L[ℝ] (Fin d → ℝ) := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : G ≃L[ℝ] G)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contDiffAt.comp_contDiffWithinAt t
    (contDiffWithinAt_pi.mpr fun i => hf _)

lemma contDiffWithinAt_inner_time (F : RicciFlow n M J) {t : ℝ}
    (ht : t ∈ J) (x : M) (v w : TangentSpace (𝓡 n) x) :
    ContDiffWithinAt ℝ ∞ (fun s => (F.metric s).inner x v w) J t := by
  have h := F.contMDiffWithinAt_inner_fields ht
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w)
  have h' := h.comp t (contMDiffWithinAt_id.prodMk contMDiffWithinAt_const)
    (show MapsTo (fun s : ℝ => (s, x)) J (J ×ˢ univ) from fun s hs => ⟨hs, mem_univ _⟩)
  simpa only [Function.comp_def, id_eq, FiberBundle.extend_apply_self] using h'.contDiffWithinAt

private lemma contDiffWithinAt_inner_connection_time
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ J) {x : M}
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x) :
    ContDiffWithinAt ℝ ∞ (fun s =>
      (F.metric s).inner x ((F.connection s).connection Y x (X x)) (Z x)) J t := by
  have hspace (s : ℝ) (U V : (x : M) → TangentSpace (𝓡 n) x)
      (hU : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% U) x)
      (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) x) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => (F.metric s).inner y (U y) (V y)) x := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric s).toRiemannianMetric⟩
    exact (hU.inner_bundle hV).mdifferentiableAt (by simp)
  have h := (((((contDiffWithinAt_mvfderiv_time ht
    (F.contMDiffWithinAt_inner_fields ht hY hZ) (fun s => hspace s Y Z hY hZ) (X x)).add
    (contDiffWithinAt_mvfderiv_time ht (F.contMDiffWithinAt_inner_fields ht hZ hX)
      (fun s => hspace s Z X hZ hX) (Y x))).sub
    (contDiffWithinAt_mvfderiv_time ht (F.contMDiffWithinAt_inner_fields ht hX hY)
      (fun s => hspace s X Y hX hY) (Z x))).add
    (F.contDiffWithinAt_inner_time ht x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x))).sub
    (F.contDiffWithinAt_inner_time ht x (VectorField.mlieBracket (𝓡 n) Y Z x) (X x))).add
    (F.contDiffWithinAt_inner_time ht x (VectorField.mlieBracket (𝓡 n) Z X x) (Y x))
  apply (h.const_smul (1 / 2 : ℝ)).congr_of_eventuallyEq_insert
  exact Filter.Eventually.of_forall fun s => by
    have hk := (F.connection s).koszul_identity
      (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
      (hZ.mdifferentiableAt (by simp))
    dsimp only [LeviCivitaData.covariantDerivativeOnFields] at hk
    simp only [smul_eq_mul]
    linarith

private lemma contDiffWithinAt_connection_apply
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ J) {x : M}
    {Y : (y : M) → TangentSpace (𝓡 n) y}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (v : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    ContDiffWithinAt ℝ ∞ (fun s => (F.connection s).connection Y x v) J t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  have hg : ContDiffWithinAt ℝ ∞ (fun s => (F.metric s).inner x) J t :=
    contDiffWithinAt_clm_of_apply fun u => contDiffWithinAt_clm_of_apply fun w =>
      F.contDiffWithinAt_inner_time ht x u w
  have hdual : ContDiffWithinAt ℝ ∞ (fun s =>
      (F.metric s).inner x ((F.connection s).connection Y x v)) J t := by
    apply contDiffWithinAt_clm_of_apply
    intro w
    have h := contDiffWithinAt_inner_connection_time F ht
      (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v) hY
      (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w)
    simpa only [FiberBundle.extend_apply_self] using h
  have hi := ((F.metric t).inner_isInvertible x).contDiffAt_map_inverse.comp_contDiffWithinAt t hg
  have h := hi.clm_apply hdual
  apply h.congr_of_eventuallyEq_insert
  exact Filter.Eventually.of_forall fun s =>
    (((F.metric s).inner_isInvertible x).inverse_apply_self _).symm

theorem contDiffWithinAt_connection
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ J) {x : M}
    {Y : (y : M) → TangentSpace (𝓡 n) y}
    (hY : ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    ContDiffWithinAt ℝ ∞ (fun s => (F.connection s).connection Y x) J t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  exact contDiffWithinAt_clm_of_apply (contDiffWithinAt_connection_apply F ht hY)

lemma contDiffWithinAt_hessian
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ J)
    (f : M → ℝ) (x : M) (u v : TangentSpace (𝓡 n) x) :
    ContDiffWithinAt ℝ ∞ (fun s => (F.connection s).hessian f x u v) J t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  have h := (F.contDiffWithinAt_connection ht
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)).clm_apply
      (contDiffWithinAt_const (c := u))
  have h' := (mvfderiv (𝓡 n) f x).contDiff.contDiffAt.comp_contDiffWithinAt t h
  have h'' := (contDiffWithinAt_const (c :=
    mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y)) x u)).sub h'
  simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    FiberBundle.extend_apply_self, Function.comp_def] at h'' ⊢
  convert h'' using 1

end PoincareConjecture.RicciFlow
