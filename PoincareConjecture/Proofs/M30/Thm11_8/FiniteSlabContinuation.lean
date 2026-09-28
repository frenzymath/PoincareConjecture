import PoincareConjecture.Proofs.M30.Generalized.ScalarAlong
import PoincareConjecture.Proofs.M30.Mathlib.GuardedScalarComparison
import PoincareConjecture.Proofs.M30.Generalized.Restriction
import PoincareConjecture.Proofs.M30.Thm5_33.CurvatureNorm

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

theorem eventually_finiteSlab_bounds_of_uniform_prefix_scalar
    (hC : RicciFlowCurvatureTheory.{u})
    {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (A T Tplus D : ℝ)
    (hA : 0 < A) (hT : 0 < T) (hTTplus : T < Tplus) (hD : 4 ≤ D)
    (hprefix : ∀ t : ℝ, 0 < t → ∀ htT : t < T,
      ∀ᶠ k : ℕ in atTop,
        ∃ e : M30FiniteHorizonSlab S k A Tplus kappa r₀,
          ∀ s (hs : s ∈ Icc (-t) 0)
            (x : ((S.flow k).slice (S.base k).1).carrier),
            x ∈ S.baseBall k A →
              (S.flow k).scalar
                ((FiniteHorizonSlab.closedEmbedding e (htT.trans hTTplus)).pointMap
                  s hs x) ≤ D * S.scale k) :
    let delta := min (T / 4)
      (min ((Tplus - T) / 4) (1 / (32 * H.analytic_constant * D)))
    0 < delta ∧ ∃ hbuffer : T + delta < Tplus,
      ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
        ∃ e : M30FiniteHorizonSlab S k A Tplus kappa r₀,
          (∀ s (hs : s ∈ Icc (-(T + delta)) 0)
            (x : ((S.flow k).slice (S.base k).1).carrier),
            |(S.flow k).curvatureNorm
              ((FiniteHorizonSlab.closedEmbedding e hbuffer).pointMap s hs x)| ≤
                (26 * D) * S.scale k) ∧
          (∀ s (hs : s ∈ Icc (-(T + delta)) 0)
            (x : ((S.flow k).slice (S.base k).1).carrier),
            let p := (FiniteHorizonSlab.closedEmbedding e hbuffer).pointMap s hs x
            ((S.flow k).connection p.1).negativeCurvaturePart p.2 ≤
              eta * S.scale k) := by
  classical
  let delta := min (T / 4)
    (min ((Tplus - T) / 4) (1 / (32 * H.analytic_constant * D)))
  change 0 < delta ∧ ∃ hbuffer : T + delta < Tplus, _
  have hDpos : 0 < D := by linarith
  have hden : 0 < 32 * H.analytic_constant * D := by
    exact mul_pos (mul_pos (by norm_num) H.analytic_constant_pos) hDpos
  have hdelta : 0 < delta :=
    lt_min (div_pos hT (by norm_num))
      (lt_min (div_pos (sub_pos.mpr hTTplus) (by norm_num)) (one_div_pos.mpr hden))
  have hdeltaT : delta ≤ T / 4 := min_le_left _ _
  have hdeltaGap : delta ≤ (Tplus - T) / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaRate : delta ≤ 1 / (32 * H.analytic_constant * D) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have htime : 16 * H.analytic_constant * D * delta ≤ 1 := by
    have hle := (le_div_iff₀ hden).mp hdeltaRate
    nlinarith
  have hbuffer : T + delta < Tplus := by linarith
  let tstar := T - delta
  have htstar : 0 < tstar := by dsimp [tstar]; linarith
  have htstarT : tstar < T := by dsimp [tstar]; linarith
  refine ⟨hdelta, hbuffer, ?_⟩
  intro eta heta
  filter_upwards [hprefix tstar htstar htstarT,
    eventually_curvatureNorm_and_negativeDefect_le hC S H.branch (2 * D)
      (by positivity) eta heta] with k hpre hcurv
  obtain ⟨e, hpre⟩ := hpre
  have hQ : 0 < S.scale k := S.base_scalar_pos k
  let I := Icc (-(T + delta)) (-T + delta)
  have hI : I ⊆ Ioc (-Tplus) 0 := by
    intro s hs
    dsimp [I] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  let eI := Cylinder.restrict e.embedding hI Subset.rfl
  have hright : -T + delta ∈ I := by
    constructor <;> linarith
  have hrightPrefix : -T + delta ∈ Icc (-tstar) 0 := by
    dsimp [tstar]
    constructor <;> linarith
  have hscalar : ∀ s (hs : s ∈ Icc (-(T + delta)) 0)
      (x : ((S.flow k).slice (S.base k).1).carrier), x ∈ S.baseBall k A →
      (S.flow k).scalar
        ((FiniteHorizonSlab.closedEmbedding e hbuffer).pointMap s hs x) ≤
          (2 * D) * S.scale k := by
    intro s hs x hx
    by_cases hleft : s ≤ -T + delta
    · let f : ℝ → ℝ := Cylinder.scalarAlong eI x
      have hchoice (z : ℝ) : ∃ d : ℝ, z ∈ I →
          HasDerivWithinAt f d I z ∧
            (4 * S.scale k ≤ f z →
              |d| ≤ H.analytic_constant / S.scale k * f z ^ 2) := by
        by_cases hz : z ∈ I
        · obtain ⟨d, hd, hrate⟩ := Cylinder.exists_scalarAlong_deriv_bound
            hC H eI hz (by dsimp [I] at hz; linarith [hz.2]) x hx
          exact ⟨d, fun _ => ⟨hd, hrate⟩⟩
        · exact ⟨0, fun hz' => (hz hz').elim⟩
      choose d hd using hchoice
      have hterminal : f (-T + delta) ≤ D * S.scale k := by
        rw [show f (-T + delta) =
            (S.flow k).scalar (eI.pointMap (-T + delta) hright x) from
          Cylinder.scalarAlong_of_mem eI x hright]
        exact hpre (-T + delta) hrightPrefix x hx
      have htime' : 8 * (H.analytic_constant / S.scale k) * (D * S.scale k) *
          ((-T + delta) - -(T + delta)) ≤ 1 := by
        calc
          _ = 16 * H.analytic_constant * D * delta := by
            field_simp [hQ.ne']
            ring
          _ ≤ 1 := htime
      have hbound := le_two_mul_of_abs_deriv_le_sq_above_backward
        (f := f) (f' := d) (div_pos H.analytic_constant_pos hQ) (mul_pos hDpos hQ)
        (mul_le_mul_of_nonneg_right hD hQ.le)
        (fun z hz => (hd z hz).1) hterminal (fun z hz => (hd z hz).2) htime'
      have hsI : s ∈ I := ⟨hs.1, hleft⟩
      have hpoint : eI.pointMap s hsI x =
          (FiniteHorizonSlab.closedEmbedding e hbuffer).pointMap s hs x := rfl
      simpa only [f, Cylinder.scalarAlong_of_mem eI x hsI, hpoint, mul_assoc] using
        hbound s hsI
    · have hsPrefix : s ∈ Icc (-tstar) 0 := by
        dsimp [tstar]
        exact ⟨by linarith, hs.2⟩
      exact (hpre s hsPrefix x hx).trans
        (mul_le_mul_of_nonneg_right (by linarith) hQ.le)
  let C := (S.flow k).slice (S.base k).1
  let U := S.baseBall k A
  have hbase : (S.base k).2 ∈ U := by
    let g : RiemannianMetric 3 C.carrier := (S.flow k).metric (S.base k).1
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : C.carrier → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change g.edist (S.base k).2 (S.base k).2 <
      ENNReal.ofReal (A / Real.sqrt (S.scale k))
    have hself : g.edist (S.base k).2 (S.base k).2 = 0 :=
      Manifold.riemannianEDist_self
    rw [hself]
    exact ENNReal.ofReal_pos.mpr (div_pos hA (Real.sqrt_pos.mpr hQ))
  let r : C.carrier → C.carrier := fun x => if x ∈ U then x else (S.base k).2
  have hr (x : C.carrier) (hx : x ∈ U) : r x = x := if_pos hx
  have hrmem (x : C.carrier) : r x ∈ U := by
    by_cases hx : x ∈ U
    · simpa only [r, if_pos hx] using hx
    · simpa only [r, if_neg hx] using hbase
  have himage (s : ℝ) (hs : s ∈ Ioc (-Tplus) 0) :
      (fun x => e.embedding.forward s hs (r x)) '' U =
        e.embedding.forward s hs '' U := by
    apply Set.image_congr
    intro x hx
    rw [hr x hx]
  let eTotal : GeneralizedFlowCylinder (S.flow k) C (S.base k).1 (S.scale k)
      (Ioc (-Tplus) 0) U := {
    scale_pos := e.embedding.scale_pos
    forward := fun s hs x => e.embedding.forward s hs (r x)
    inverse := e.embedding.inverse
    forward_smooth := by
      intro s hs
      exact (e.embedding.forward_smooth s hs).congr (fun x hx => by rw [hr x hx])
    inverse_smooth := by
      intro s hs
      rw [himage s hs]
      exact e.embedding.inverse_smooth s hs
    left_inverse := by
      intro s hs x hx
      change e.embedding.inverse s hs (e.embedding.forward s hs (r x)) = x
      rw [hr x hx]
      exact e.embedding.left_inverse s hs hx
    right_inverse := by
      intro s hs y hy
      rw [himage s hs] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      change e.embedding.forward s hs
        (r (e.embedding.inverse s hs (e.embedding.forward s hs x))) = _
      rw [e.embedding.left_inverse s hs hx, hr x hx]
    embedding := by
      have hmap :
          (fun p : Ioc (-Tplus) 0 × U =>
            (⟨(S.base k).1 + p.1.1 / S.scale k,
              e.embedding.forward p.1.1 p.1.2 (r p.2.1)⟩ : (S.flow k).point)) =
          (fun p : Ioc (-Tplus) 0 × U =>
            (⟨(S.base k).1 + p.1.1 / S.scale k,
              e.embedding.forward p.1.1 p.1.2 p.2.1⟩ : (S.flow k).point)) := by
        funext p
        rw [hr p.2.1 p.2.2]
      rw [hmap]
      exact e.embedding.embedding
    vertical_compatibility := by
      intro s hs x hx
      simpa only [hr x hx] using e.embedding.vertical_compatibility s hs x hx }
  let e' : M30FiniteHorizonSlab S k A Tplus kappa r₀ := {
    embedding := eTotal
    zero_identity := by
      intro hzero x hx
      change e.embedding.pointMap 0 hzero (r x) = _
      rw [hr x hx]
      exact e.zero_identity hzero x hx
    noncollapsed := by
      intro s hs x hx
      change GeneralizedKappaNoncollapsedAt (S.flow k)
        (e.embedding.pointMap s hs (r x)) kappa r₀
      rw [hr x hx]
      exact e.noncollapsed s hs x hx }
  have hbounds (s : ℝ) (hs : s ∈ Icc (-(T + delta)) 0) (x : C.carrier) :
      let p := (FiniteHorizonSlab.closedEmbedding e' hbuffer).pointMap s hs x
      |(S.flow k).curvatureNorm p| ≤ (26 * D) * S.scale k ∧
        ((S.flow k).connection p.1).negativeCurvaturePart p.2 ≤ eta * S.scale k := by
    let p := (FiniteHorizonSlab.closedEmbedding e' hbuffer).pointMap s hs x
    have hp : p.1 ∈ (S.flow k).interval :=
      ((S.flow k).slice_nonempty_iff p.1).mp ⟨p.2⟩
    have hR : (S.flow k).scalar p ≤ (2 * D) * S.scale k :=
      hscalar s hs (r x) (hrmem x)
    have h := hcurv p.1 hp p.2 hR
    have hmax : max (2 * D) 1 = 2 * D := max_eq_left (by linarith)
    simpa only [hmax, show 13 * (2 * D) = 26 * D by ring] using h
  exact ⟨e', fun s hs x => (hbounds s hs x).1, fun s hs x => (hbounds s hs x).2⟩

end PoincareConjecture.M30
