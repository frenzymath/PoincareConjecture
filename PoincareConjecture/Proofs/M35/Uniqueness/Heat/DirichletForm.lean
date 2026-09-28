import PoincareConjecture.Proofs.M03.Existence.EuclideanDerivativeClosedNative
import PoincareConjecture.Proofs.M03.Existence.EuclideanRellichNative
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Topology.Sequences











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)



def supportedTests (K : Set V) : Submodule ℝ (𝓢(V, ℝ)) where
  carrier := {f | ∀ x ∉ K, f x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f h hf hh x hx
    change f x + h x = 0
    rw [hf x hx, hh x hx, add_zero]
  smul_mem' := by
    intro c f hf x hx
    change c • f x = 0
    rw [hf x hx, smul_zero]


def testValue (K : Set V) : supportedTests K →ₗ[ℝ] L2 :=
  (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure V)).toLinearMap.comp
    (supportedTests K).subtype


def dirichletValue (K : Set V) : Submodule ℝ L2 := (testValue K).range.topologicalClosure

instance dirichletValue_completeSpace (K : Set V) : CompleteSpace (dirichletValue K) :=
  inferInstanceAs (CompleteSpace (testValue K).range.topologicalClosure)

def intoDirichletValue (K : Set V) : supportedTests K →ₗ[ℝ] dirichletValue K :=
  (testValue K).codRestrict (dirichletValue K) (fun f =>
    (testValue K).range.le_topologicalClosure (LinearMap.mem_range_self _ f))

theorem intoDirichletValue_denseRange (K : Set V) : DenseRange (intoDirichletValue K) := by
  apply Topology.IsInducing.subtypeVal.dense_iff.mpr
  intro x
  have hincl : ((testValue K).range : Set L2) ⊆
      Subtype.val '' Set.range (intoDirichletValue K) := by
    rintro _ ⟨f, rfl⟩
    exact ⟨intoDirichletValue K f, ⟨f, rfl⟩, rfl⟩
  exact closure_mono hincl x.property

abbrev DirichletGradient (n : ℕ) :=
  PiLp 2 (fun _ : Fin n => Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))


def testGradient (K : Set V) : supportedTests K →ₗ[ℝ] DirichletGradient n :=
  (WithLp.linearEquiv 2 ℝ (Fin n → L2)).symm.toLinearMap.comp
    (LinearMap.pi (fun i => (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure V)).toLinearMap.comp
      ((LineDeriv.lineDerivOpCLM ℝ 𝓢(V, ℝ) (EuclideanSpace.single i (1 : ℝ))).toLinearMap.comp
        (supportedTests K).subtype)))

@[simp] theorem testGradient_apply (K : Set V) (f : supportedTests K) (i : Fin n) :
    testGradient K f i = (∂_{EuclideanSpace.single i (1 : ℝ)} (f : 𝓢(V, ℝ))).toLp 2 volume := rfl

abbrev DirichletAmbient (K : Set V) := WithLp 2 (dirichletValue K × DirichletGradient n)

def dirichletImage (K : Set V) : supportedTests K →ₗ[ℝ] DirichletAmbient K :=
  (WithLp.linearEquiv 2 ℝ (dirichletValue K × DirichletGradient n)).symm.toLinearMap.comp
    ((intoDirichletValue K).prod (testGradient K))


def dirichletForm (K : Set V) : Submodule ℝ (DirichletAmbient K) :=
  (dirichletImage K).range.topologicalClosure

instance dirichletForm_completeSpace (K : Set V) : CompleteSpace (dirichletForm K) :=
  inferInstanceAs (CompleteSpace (dirichletImage K).range.topologicalClosure)

def intoDirichletForm (K : Set V) : supportedTests K →ₗ[ℝ] dirichletForm K :=
  (dirichletImage K).codRestrict (dirichletForm K) (fun f =>
    (dirichletImage K).range.le_topologicalClosure (LinearMap.mem_range_self _ f))

theorem intoDirichletForm_denseRange (K : Set V) : DenseRange (intoDirichletForm K) := by
  apply Topology.IsInducing.subtypeVal.dense_iff.mpr
  intro x
  have hincl : ((dirichletImage K).range : Set (DirichletAmbient K)) ⊆
      Subtype.val '' Set.range (intoDirichletForm K) := by
    rintro _ ⟨f, rfl⟩
    exact ⟨intoDirichletForm K f, ⟨f, rfl⟩, rfl⟩
  exact closure_mono hincl x.property

def dirichletInclusion (K : Set V) : dirichletForm K →L[ℝ] dirichletValue K :=
  (WithLp.fstL 2 ℝ (dirichletValue K) (DirichletGradient n)).comp
    (dirichletForm K).subtypeL

@[simp] theorem dirichletInclusion_into (K : Set V) (f : supportedTests K) :
    dirichletInclusion K (intoDirichletForm K f) = intoDirichletValue K f := rfl

theorem norm_dirichletInclusion_apply_le (K : Set V) (v : dirichletForm K) :
    ‖dirichletInclusion K v‖ ≤ ‖v‖ :=
  WithLp.norm_fst_le (dirichletValue K) (v : DirichletAmbient K)

theorem norm_dirichletInclusion_le_one (K : Set V) : ‖dirichletInclusion K‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [one_mul] using norm_dirichletInclusion_apply_le K v

theorem dirichletInclusion_denseRange (K : Set V) : DenseRange (dirichletInclusion K) := by
  apply (intoDirichletValue_denseRange K).mono
  rintro _ ⟨f, rfl⟩
  exact ⟨intoDirichletForm K f, rfl⟩



theorem dirichletInclusion_eq_zero_iff (K : Set V) (v : dirichletForm K) :
    dirichletInclusion K v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have hcl : (v : DirichletAmbient K) ∈ closure (Set.range (dirichletImage K)) := v.property
    obtain ⟨s, hs, hslim⟩ := mem_closure_iff_seq_limit.mp hcl
    choose f hf using hs
    have hflim : Tendsto (fun j => dirichletImage K (f j)) atTop
        (𝓝 (v : DirichletAmbient K)) :=
      hslim.congr' (Eventually.of_forall (fun j => (hf j).symm))
    let P : DirichletAmbient K →L[ℝ] L2 := (dirichletValue K).subtypeL.comp
      (WithLp.fstL 2 ℝ (dirichletValue K) (DirichletGradient n))
    let Q : DirichletAmbient K →L[ℝ] DirichletGradient n :=
      WithLp.sndL 2 ℝ (dirichletValue K) (DirichletGradient n)
    have hPv : P (v : DirichletAmbient K) = 0 :=
      congrArg (fun z : dirichletValue K => (z : L2)) hv
    have hvalues : Tendsto (fun j => (f j : 𝓢(V, ℝ)).toLp 2 volume) atTop (𝓝 0) := by
      have h := (P.continuous.tendsto (v : DirichletAmbient K)).comp hflim
      rw [hPv] at h
      exact h
    have hgradients : Tendsto (fun j => testGradient K (f j)) atTop
        (𝓝 (Q (v : DirichletAmbient K))) :=
      (Q.continuous.tendsto (v : DirichletAmbient K)).comp hflim
    have hQv : Q (v : DirichletAmbient K) = 0 := by
      apply PiLp.ext
      intro i
      let C : DirichletGradient n →L[ℝ] L2 := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => L2) i
      have hc := (C.continuous.tendsto (Q (v : DirichletAmbient K))).comp hgradients
      exact EuclideanDerivativeNative.schwartzLineDeriv_limit_zero
        (EuclideanSpace.single i 1) (fun j => (f j : 𝓢(V, ℝ)))
        (Q (v : DirichletAmbient K) i) hvalues hc
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    exact Prod.ext hv hQv
  · rintro rfl
    exact map_zero _

theorem dirichletInclusion_injective (K : Set V) :
    Function.Injective (dirichletInclusion K) := by
  intro v w he
  apply sub_eq_zero.mp
  apply (dirichletInclusion_eq_zero_iff K (v - w)).mp
  rw [map_sub, he, sub_self]



theorem testGradient_norm_sq (K : Set V) (f : supportedTests K) :
    ‖testGradient K f‖ ^ 2 = EuclideanMollificationNative.gradientEnergy (f : V → ℝ) := by
  rw [PiLp.norm_sq_eq_of_L2]
  unfold EuclideanMollificationNative.gradientEnergy
  apply Finset.sum_congr rfl
  intro i _
  rw [testGradient_apply, EuclideanTranslationNative.scalarLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [(∂_{EuclideanSpace.single i (1 : ℝ)} (f : 𝓢(V, ℝ))).coeFn_toLp 2 volume]
    with x hx
  rw [hx, SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem dirichletImage_norm_sq (K : Set V) (f : supportedTests K) :
    ‖dirichletImage K f‖ ^ 2 = ‖testValue K f‖ ^ 2 +
      EuclideanMollificationNative.gradientEnergy (f : V → ℝ) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖testValue K f‖ ^ 2 + ‖testGradient K f‖ ^ 2 = _
  rw [testGradient_norm_sq]

end PoincareConjecture.M35.Uniqueness.Heat
