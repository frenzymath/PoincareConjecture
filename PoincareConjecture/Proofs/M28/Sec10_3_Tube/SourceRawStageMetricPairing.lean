import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallRawStage
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallMetricIdentity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 3200000 in

theorem regularRawStageDiffeomorph_metric_pairing
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (Acrit : ℝ) (hAcrit : 0 < Acrit)
    (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T Acrit (phi k))
      (fun k => H.tubeCriticalBase T Acrit hAcrit (phi k))) (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    let i := phi (G.subsequence k)
    let e := H.regularRawStageDiffeomorph T Acrit hAcrit phi G k
    ∀ x ∈ G.exhaustion k, ∀ v w : TangentSpace (𝓡 3) x,
      (H.tubeCriticalMetric T Acrit i).inner (G.embedding k x)
        (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) x v)
        (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) x w) =
      (E (i + H.shift)).flow.scalar
          ⟨(E (i + H.shift)).time, (E (i + H.shift)).basepoint⟩ *
        ((E (i + H.shift)).flow.metric (E (i + H.shift)).time).inner (e x)
          (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro i e x hx v w
  let i₁ : H.tubeCriticalRegion T Acrit i → (T i).carrierOpen := Subtype.val
  let i₂ : (T i).carrierOpen →
      ((E (i + H.shift)).flow.slice (E (i + H.shift)).time).carrier := Subtype.val
  have h₁ := openSubtype_isLocalDiffeomorph (H.tubeCriticalRegion T Acrit i)
  have h₂ := openSubtype_isLocalDiffeomorph (T i).carrierOpen
  have hf : MDifferentiableAt (𝓡 3) (𝓡 3) (G.embedding k) x :=
    (G.stageDiffeomorph k).mdifferentiableAt (by simp) hx
  have he : (e : G.limitCarrier.carrier →
      ((E (i + H.shift)).flow.slice (E (i + H.shift)).time).carrier) =
        i₂ ∘ (i₁ ∘ G.embedding k) := by
    funext y
    exact H.regularRawStageDiffeomorph_apply T Acrit hAcrit phi G k y
  have hderiv (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) e x z =
        mfderiv (𝓡 3) (𝓡 3) i₂ (i₁ (G.embedding k x))
          (mfderiv (𝓡 3) (𝓡 3) i₁ (G.embedding k x)
            (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) x z)) := by
    have hfirst := mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3)
      (f := G.embedding k) (g := i₁) x
      ((h₁ (G.embedding k x)).mdifferentiableAt (by simp)) hf z
    have hsecond := mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3)
      (f := i₁ ∘ G.embedding k) (g := i₂) x
      ((h₂ (i₁ (G.embedding k x))).mdifferentiableAt (by simp))
      (((h₁ (G.embedding k x)).mdifferentiableAt (by simp)).comp x hf) z
    have heD : mfderiv (𝓡 3) (𝓡 3) e x z =
        mfderiv (𝓡 3) (𝓡 3) (i₂ ∘ (i₁ ∘ G.embedding k)) x z :=
      congrArg (fun f : G.limitCarrier.carrier →
          ((E (i + H.shift)).flow.slice (E (i + H.shift)).time).carrier =>
        mfderiv (𝓡 3) (𝓡 3) f x z) he
    exact heD.trans (hsecond.trans (congrArg
      (mfderiv (𝓡 3) (𝓡 3) i₂ (i₁ (G.embedding k x))) hfirst))
  let Q := (E (i + H.shift)).flow.scalar
    ⟨(E (i + H.shift)).time, (E (i + H.shift)).basepoint⟩
  let g₀ := (E (i + H.shift)).flow.metric (E (i + H.shift)).time
  let push (z : TangentSpace (𝓡 3) x) :=
    mfderiv (𝓡 3) (𝓡 3) i₂ (i₁ (G.embedding k x))
      (mfderiv (𝓡 3) (𝓡 3) i₁ (G.embedding k x)
        (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) x z))
  have hmetric : (H.tubeCriticalMetric T Acrit i).inner (G.embedding k x)
      (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) x v)
      (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) x w) =
      Q * g₀.inner (i₂ (i₁ (G.embedding k x))) (push v) (push w) := by
    rfl
  have hpoint : i₂ (i₁ (G.embedding k x)) = e x := (congrFun he x).symm
  have hpair : g₀.inner (i₂ (i₁ (G.embedding k x))) (push v) (push w) =
      g₀.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)
        (mfderiv (𝓡 3) (𝓡 3) e x w) :=
    (congrArg (fun p :
        ((E (i + H.shift)).flow.slice (E (i + H.shift)).time).carrier =>
      g₀.inner p (push v) (push w)) hpoint).trans
        (congrArg₂ (fun a b : EuclideanSpace ℝ (Fin 3) => g₀.inner (e x) a b)
          (hderiv v).symm (hderiv w).symm)
  exact hmetric.trans (congrArg (fun r : ℝ => Q * r) hpair)

set_option maxHeartbeats 3200000 in

theorem regularRawStageDiffeomorph_relative_inner_bounds
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (Acrit : ℝ) (hAcrit : 0 < Acrit)
    (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T Acrit (phi k))
      (fun k => H.tubeCriticalBase T Acrit hAcrit (phi k))) (k : ℕ) (delta : ℝ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    let i := phi (G.subsequence k)
    let e := H.regularRawStageDiffeomorph T Acrit hAcrit phi G k
    let Q := (E (i + H.shift)).flow.scalar
      ⟨(E (i + H.shift)).time, (E (i + H.shift)).basepoint⟩
    ∀ K : Set G.limitCarrier.carrier, K ⊆ G.exhaustion k →
    (∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
      (1 + delta)⁻¹ * G.limitMetric.inner x v v ≤
        (H.tubeCriticalMetric T Acrit i).inner (G.embedding k x)
          (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) x v)
          (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) x v) ∧
      (H.tubeCriticalMetric T Acrit i).inner (G.embedding k x)
          (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) x v)
          (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) x v) ≤
        (1 + delta) * G.limitMetric.inner x v v) →
    ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
      (1 + delta)⁻¹ * G.limitMetric.inner x v v ≤
        Q * ((E (i + H.shift)).flow.metric (E (i + H.shift)).time).inner (e x)
          (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x v) ∧
      Q * ((E (i + H.shift)).flow.metric (E (i + H.shift)).time).inner (e x)
          (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤
        (1 + delta) * G.limitMetric.inner x v v := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro i e Q K hK hrelative x hx v
  have hh := hrelative x hx v
  rw [H.regularRawStageDiffeomorph_metric_pairing T Acrit hAcrit phi G k x (hK hx) v v] at hh
  exact hh

end PoincareConjecture.M28.CounterexampleNeckFamily
