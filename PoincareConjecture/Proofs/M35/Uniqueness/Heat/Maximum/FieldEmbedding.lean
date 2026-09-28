import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TestGenerator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Z" => EuclideanSpace ℝ (Fin m)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

def scalarFieldsLp : PiLp 2 (fun _ : Fin m => L2) →L[ℝ] Lp Z 2 (volume : Measure V) :=
  ∑ i, ((finiteHilbertSingle (H := ℝ) i).compLpL 2 (volume : Measure V)).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => L2) i)

theorem scalarFieldsLp_coe (f : PiLp 2 (fun _ : Fin m => L2)) :
    scalarFieldsLp f =ᵐ[volume] fun x => WithLp.toLp 2 (fun i => f i x) := by
  have hcomp : ∀ᵐ x ∂volume, ∀ i : Fin m,
      (finiteHilbertSingle (H := ℝ) i).compLpL 2 (volume : Measure V) (f i) x =
        finiteHilbertSingle i (f i x) :=
    ae_all_iff.mpr fun i => (finiteHilbertSingle (H := ℝ) i).coeFn_compLpL (f i)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i => (finiteHilbertSingle (H := ℝ) i).compLpL 2 (volume : Measure V) (f i)),
    hcomp] with x hx hc
  simp only [scalarFieldsLp, sum_apply, ContinuousLinearMap.comp_apply]
  change (∑ i, (finiteHilbertSingle (H := ℝ) i).compLpL 2 (volume : Measure V) (f i)) x = _
  rw [hx]
  simp only [hc]
  apply PiLp.ext
  intro j
  simp [finiteHilbertSingle_apply]

def schwartzField (f : Fin m → 𝓢(V, ℝ)) : 𝓢(V, Z) :=
  ∑ i, SchwartzMap.postcompCLM (finiteHilbertSingle (H := ℝ) i) (f i)

@[simp] theorem schwartzField_apply (f : Fin m → 𝓢(V, ℝ)) (x : V) :
    schwartzField f x = WithLp.toLp 2 (fun i => f i x) := by
  apply PiLp.ext
  intro j
  simp [schwartzField, sum_apply, finiteHilbertSingle_apply]

theorem schwartzField_toLp (f : Fin m → 𝓢(V, ℝ)) :
    (schwartzField f).toLp 2 volume =
      scalarFieldsLp (WithLp.toLp 2 (fun i => (f i).toLp 2 volume)) := by
  apply Lp.ext
  have hf : ∀ᵐ x ∂volume, ∀ i : Fin m, (f i).toLp 2 volume x = f i x :=
    ae_all_iff.mpr fun i => (f i).coeFn_toLp 2 volume
  filter_upwards [(schwartzField f).coeFn_toLp 2 volume,
    scalarFieldsLp_coe (WithLp.toLp 2 (fun i => (f i).toLp 2 volume)), hf] with x hx hy hf
  rw [hx, hy, schwartzField_apply]
  apply PiLp.ext
  exact fun i => (hf i).symm

private theorem partial_postcomp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ℝ →L[ℝ] F) (f : 𝓢(V, ℝ)) (v : V) :
    ∂_{v} (SchwartzMap.postcompCLM L f) = SchwartzMap.postcompCLM L (∂_{v} f) := by
  ext x
  change fderiv ℝ (fun y => L (f y)) x v = L (fderiv ℝ f x v)
  have h := (L.hasFDerivAt).comp x (f.smooth'.differentiable (by simp) x).hasFDerivAt
  simp only [Function.comp_def] at h
  exact congrArg (fun A : V →L[ℝ] F => A v) h.fderiv

theorem schwartzField_partial (f : Fin m → 𝓢(V, ℝ)) (v : V) :
    ∂_{v} (schwartzField f) = schwartzField (fun i => ∂_{v} (f i)) := by
  change (LineDeriv.lineDerivOpCLM ℝ 𝓢(V, Z) v) (∑ i, _) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => partial_postcomp _ _ _

theorem schwartzField_hasCompactSupport {K : Set V} (hK : IsCompact K)
    (f : Fin m → supportedTests K) :
    HasCompactSupport (schwartzField (fun i => (f i : 𝓢(V, ℝ)))) := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hn
  exact hx (by
    rw [schwartzField_apply]
    apply PiLp.ext
    intro i
    exact (f i).property x hn)

def dirichletFieldValue (K : Set V) :
    PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ] Lp Z 2 (volume : Measure V) :=
  scalarFieldsLp.comp (finiteHilbertMap ((dirichletValue K).subtypeL.comp (dirichletInclusion K)))

def dirichletFieldPartial (K : Set V) (j : Fin n) :
    PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ] Lp Z 2 (volume : Measure V) :=
  scalarFieldsLp.comp (finiteHilbertMap (dirichletPartial K j))

theorem dirichletFieldValue_test (K : Set V) (f : Fin m → supportedTests K) :
    dirichletFieldValue K (vectorTestForm K f) =
      (schwartzField (fun i => (f i : 𝓢(V, ℝ)))).toLp 2 volume :=
  (schwartzField_toLp _).symm

theorem dirichletFieldPartial_test (K : Set V) (f : Fin m → supportedTests K) (j : Fin n) :
    dirichletFieldPartial K j (vectorTestForm K f) =
      (∂_{EuclideanSpace.single j (1 : ℝ)}
        (schwartzField (fun i => (f i : 𝓢(V, ℝ))))).toLp 2 volume := by
  rw [schwartzField_partial, schwartzField_toLp]
  rfl

end PoincareConjecture.M35.Uniqueness.Heat
