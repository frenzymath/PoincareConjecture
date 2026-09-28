
import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Curvature.SecondBianchi
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Connection.MetricDuality
import PoincareConjecture.Proofs.M05.Geometry.Manifold.VectorField.Derivation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private lemma contDiffAt_clm_of_apply
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ E]
    {f : ℝ → E →L[ℝ] G} {t : ℝ}
    (hf : ∀ v, ContDiffAt ℝ ∞ (fun s => f s v) t) :
    ContDiffAt ℝ ∞ f t := by
  let d := Module.finrank ℝ E
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ : E ≃L[ℝ] (Fin d → ℝ) := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : G ≃L[ℝ] G)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contDiffAt.comp t
    (contDiffAt_pi.mpr fun i => hf _)

lemma contMDiffAt_inner_fields (F : RicciFlow n M J) {t : ℝ}
    (ht : t ∈ interior J) {x : M}
    {X Y : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.metric p.1).inner p.2 (X p.2) (Y p.2)) (t, x) := by
  have hg := (F.smooth (t, x) ⟨interior_subset ht, mem_univ x⟩).contMDiffAt
    (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht) univ_mem)
  have hX' : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.2))
      (t, x) := hX.comp (t, x) contMDiffAt_snd
  have hY' : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Y p.2))
      (t, x) := hY.comp (t, x) contMDiffAt_snd
  have h := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : M => ℝ) hX' hY'
  exact (contMDiffAt_totalSpace.mp h).2

private lemma contDiffAt_mvfderiv_time
    {f : ℝ × M → ℝ} {t : ℝ} {x : M}
    (hf : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (t, x))
    (v : TangentSpace (𝓡 n) x) :
    ContDiffAt ℝ ∞ (fun s => mvfderiv (𝓡 n) (fun y => f (s, y)) x v) t := by
  let e := extChartAt (𝓡 n) x
  have hx : e.symm (e x) = x := e.left_inv (mem_extChartAt_source x)
  have hs : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ e.symm (e x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  have hc : ContDiffAt ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => f (p.1, e.symm p.2)) (t, e x) := by
    have hp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, e.symm p.2)) (t, e x) :=
      contMDiffAt_fst.prodMk (hs.comp (t, e x) contMDiffAt_snd)
    have h := hf.comp_of_eq hp (by simp [hx])
    simp +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffAt
  have hd := hc.fderiv (f := fun s z => f (s, e.symm z))
    (g := fun _ : ℝ => e x) contDiffAt_const (m := ∞) (by simp)
  let w : EuclideanSpace ℝ (Fin n) :=
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) e.symm (e x)).inverse v
  have hh := hd.clm_apply (contDiffAt_const (c := w))
  apply hh.congr_of_eventuallyEq
  have hevent : ∀ᶠ s in 𝓝 t,
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => f (s, y)) x := by
    have hnear := ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp
      (hf.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)))
    have htime : Tendsto (fun s : ℝ => (s, x)) (𝓝 t) (𝓝 (t, x)) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [htime.eventually hnear] with s hs
    exact (hs.comp x (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  filter_upwards [hevent] with s hs
  have h := Poincare.Manifold.VectorField.fderiv_comp_extChartAt_symm
    (p := x) (by simpa [e, hx] using hs) (mem_extChartAt_target x) w
  have hi := Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm
    (I := 𝓡 n) (p := x) (mem_extChartAt_target x)
  change fderiv ℝ ((fun y => f (s, y)) ∘ e.symm) (e x) w =
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun y => f (s, y)) (e.symm (e x))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) e.symm (e x) w) at h
  dsimp only [w] at h
  rw [hi.self_apply_inverse, hx] at h
  exact h.symm

lemma contDiffAt_inner_time (F : RicciFlow n M J) {t : ℝ}
    (ht : t ∈ interior J) (x : M) (v w : TangentSpace (𝓡 n) x) :
    ContDiffAt ℝ ∞ (fun s => (F.metric s).inner x v w) t := by
  have h := F.contMDiffAt_inner_fields ht
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w)
  have h' := h.comp t (contMDiffAt_id.prodMk contMDiffAt_const)
  simpa only [Function.comp_def, id_eq, FiberBundle.extend_apply_self] using h'.contDiffAt


lemma contDiffAt_inner (F : RicciFlow n M J) {t : ℝ}
    (ht : t ∈ interior J) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
    letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
    letI : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
    letI : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
    ContDiffAt ℝ ∞ (fun s => (F.metric s).inner x) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  exact contDiffAt_clm_of_apply fun v => contDiffAt_clm_of_apply fun w =>
    contDiffAt_inner_time F ht x v w

private lemma contDiffAt_inner_connection_time
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) {x : M}
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x) :
    ContDiffAt ℝ ∞ (fun s =>
      (F.metric s).inner x ((F.connection s).connection Y x (X x)) (Z x)) t := by
  have h := (((((contDiffAt_mvfderiv_time
    (F.contMDiffAt_inner_fields ht hY hZ) (X x)).add
    (contDiffAt_mvfderiv_time (F.contMDiffAt_inner_fields ht hZ hX) (Y x))).sub
    (contDiffAt_mvfderiv_time (F.contMDiffAt_inner_fields ht hX hY) (Z x))).add
    (contDiffAt_inner_time F ht x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x))).sub
    (contDiffAt_inner_time F ht x (VectorField.mlieBracket (𝓡 n) Y Z x) (X x))).add
    (contDiffAt_inner_time F ht x (VectorField.mlieBracket (𝓡 n) Z X x) (Y x))
  apply (h.const_smul (1 / 2 : ℝ)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun s => by
    have hk := (F.connection s).koszul_identity
      (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
      (hZ.mdifferentiableAt (by simp))
    dsimp only [LeviCivitaData.covariantDerivativeOnFields] at hk
    simp only [smul_eq_mul]
    linarith

private lemma contDiffAt_connection_apply
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) {x : M}
    {Y : (y : M) → TangentSpace (𝓡 n) y}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (v : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    ContDiffAt ℝ ∞ (fun s => (F.connection s).connection Y x v) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  have hg : ContDiffAt ℝ ∞ (fun s => (F.metric s).inner x) t :=
    contDiffAt_clm_of_apply fun u => contDiffAt_clm_of_apply fun w =>
      contDiffAt_inner_time F ht x u w
  have hdual : ContDiffAt ℝ ∞ (fun s =>
      (F.metric s).inner x ((F.connection s).connection Y x v)) t := by
    apply contDiffAt_clm_of_apply
    intro w
    have h := contDiffAt_inner_connection_time F ht
      (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v) hY
      (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w)
    simpa only [FiberBundle.extend_apply_self] using h
  have hi := ((F.metric t).inner_isInvertible x).contDiffAt_map_inverse.comp t hg
  have h := hi.clm_apply hdual
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun s =>
    (((F.metric s).inner_isInvertible x).inverse_apply_self _).symm



theorem contDiffAt_connection
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) {x : M}
    {Y : (y : M) → TangentSpace (𝓡 n) y}
    (hY : ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    ContDiffAt ℝ ∞ (fun s => (F.connection s).connection Y x) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  exact contDiffAt_clm_of_apply (contDiffAt_connection_apply F ht hY)

end PoincareConjecture.RicciFlow
