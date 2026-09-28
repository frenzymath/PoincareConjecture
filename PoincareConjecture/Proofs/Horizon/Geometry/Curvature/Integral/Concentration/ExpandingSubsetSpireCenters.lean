import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.SubsetSpireCenters
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.SuppliedRebase









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open Poincare.GromovHausdorff
namespace Poincare.CurvatureIntegral
private theorem base_ascent_of_bad_radius_zero
    {X : ℕ → BasedMetricSpaceBundle.{0}} {Y : BasedMetricSpaceBundle.{0}}
    [∀ j, ProperSpace (X j).carrier] [ProperSpace Y.carrier]
    (hconv : PointedGHConvergesUnbounded X Y)
    {b c c' : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (hcc' : c' < c)
    (ha : Tendsto (fun j => badAscentRadius c b (X j).base) atTop (𝓝 0)) :
    ∀ y : Y.carrier, 0 < dist Y.base y → dist Y.base y < b →
      HasLocalDistanceAscent c' Y.base y := by
  let L := 2 * b + 1
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨δ, hδ, hpos, hball⟩ := hconv L hL
  let S := realizationSequenceOfPointedGHConverges
    (fun j => ballModel (X j) (L + δ j) (hpos j)) (ballModel Y L hL) hball
  have hbase : S.PointConverges
      (fun j => (ballModel (X j) (L + δ j) (hpos j)).base)
      (ballModel Y L hL).base := by
    unfold VaryingRealizationSequence.PointConverges
    have heq : (fun j => dist
        (S.left j (ballModel (X j) (L + δ j) (hpos j)).base)
        (S.right j (ballModel Y L hL).base)) = fun _ => (0 : ℝ) := by
      funext j
      exact dist_eq_zero.mpr (S.base_agree j)
    rw [heq]
    exact tendsto_const_nhds
  exact local_distance_ascent_of_tendsto_badAscentRadius_zero
    hL δ hδ hpos S _ _ hbase hc hcc'
    (by change dist Y.base Y.base + b < L; simp only [dist_self, zero_add]; dsimp [L]; linarith) ha



theorem tendsto_dist_zero_of_badAscentRadius_zero_at_scaled_spire_in_expanding_subset
    {X : ℕ → BasedMetricSpaceBundle.{0}} {Y : BasedMetricSpaceBundle.{0}}
    [∀ j, ProperSpace (X j).carrier] [ProperSpace Y.carrier]
    (hXgeo : ∀ j, ∀ x y : (X j).carrier,
      ∃ γ : ℝ → (X j).carrier, γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    (hYgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier,
      γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    {R : ℝ} (hR : 0 ≤ R) (E : ∀ j, Set (X j).carrier)
    (hE : ∀ j x, x ∈ E j → dist (X j).base x ≤ R)
    {s t : ℕ → ℝ} (hs : ∀ j, R < s j) (ht : ∀ j, R < t j)
    (hsTop : Tendsto s atTop atTop) (htTop : Tendsto t atTop atTop)
    (Q : ∀ j, PointedGHRealization
      (ballModel (X j) (s j) (lt_of_le_of_lt hR (hs j)))
      (ballModel Y (t j) (lt_of_le_of_lt hR (ht j))))
    (hQ : Tendsto (fun j => pointedHausdorffDist (Q j)) atTop (𝓝 0))
    (K : Set Y.carrier) (hK : IsCompact K)
    (hKR : K ⊆ Metric.closedBall Y.base R)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hforward : ∀ j (x : E j), ∃ z : K,
      dist ((Q j).left ⟨x.val, Metric.mem_ball'.mpr ((hE j x.val x.property).trans_lt (hs j))⟩)
        ((Q j).right ⟨z.val, Metric.mem_ball'.mpr
          ((Metric.mem_closedBall'.mp (hKR z.property)).trans_lt (ht j))⟩) < ε j)
    (y₀ : K) (v u : ∀ j, E j)
    (href : ∀ j,
      dist ((Q j).left ⟨(v j).val, Metric.mem_ball'.mpr
          ((hE j (v j).val (v j).property).trans_lt (hs j))⟩)
        ((Q j).right ⟨y₀.val, Metric.mem_ball'.mpr
          ((Metric.mem_closedBall'.mp (hKR y₀.property)).trans_lt (ht j))⟩) < ε j)
    {κ ρ b cap c c' : ℝ} (hκ : 0 < κ) (_hρ : 0 < ρ) (hb : 0 < b)
    (hρb : ρ < κ * b / 2) (hbcap : b ≤ cap)
    (hnear : ∀ j, dist (v j).val (u j).val ≤ ρ)
    (hc : 0 ≤ c) (hcc' : c' < c) (B : Y.carrier → ℝ)
    (hmax : ∀ p : Y.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
      (∀ y : Y.carrier, 0 < dist p y → dist p y < 2 * a →
        HasLocalDistanceAscent c' p y) → a ≤ B p)
    (hspire : ∀ y ∈ K, y ≠ y₀.val → κ * B y ≤ dist y y₀.val)
    (ha : Tendsto (fun j => badAscentRadius c b (u j).val) atTop (𝓝 0)) :
    Tendsto (fun j => dist (v j).val (u j).val) atTop (𝓝 0) := by
  classical
  let e (j : ℕ) (x : E j) :
      (ballModel (X j) (s j) (lt_of_le_of_lt hR (hs j))).carrier :=
    ⟨x.val, Metric.mem_ball'.mpr ((hE j x.val x.property).trans_lt (hs j))⟩
  let k (j : ℕ) (z : K) :
      (ballModel Y (t j) (lt_of_le_of_lt hR (ht j))).carrier :=
    ⟨z.val, Metric.mem_ball'.mpr
      ((Metric.mem_closedBall'.mp (hKR z.property)).trans_lt (ht j))⟩
  choose z hz using fun j => hforward j (u j)
  have hcross (j : ℕ) : dist ((Q j).left (e j (u j))) ((Q j).right (k j (z j))) < ε j :=
    hz j
  apply Metric.tendsto_nhds.mpr
  intro η hη
  by_contra hnot
  have hnot' : ¬ ∀ᶠ j in atTop, dist (v j).val (u j).val < η := by
    intro hevent
    apply hnot
    filter_upwards [hevent] with j hj
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hj
  obtain ⟨φ, hφ, hbad⟩ := Filter.extraction_of_frequently_atTop
    (Filter.not_eventually.mp hnot')
  obtain ⟨z₀, hz₀, ψ, hψ, hzlim⟩ :=
    hK.isSeqCompact (fun j => (z (φ j)).property)
  let θ := fun j => φ (ψ j)
  have hθ : Tendsto θ atTop atTop := hφ.tendsto_atTop.comp hψ.tendsto_atTop
  let zK : K := ⟨z₀, hz₀⟩
  have hzdist : Tendsto (fun j => dist (z (θ j)).val z₀) atTop (𝓝 0) := by
    simpa only [Function.comp_def, dist_self, θ] using hzlim.dist (tendsto_const_nhds (x := z₀))
  have huCross : Tendsto
      (fun j => dist ((Q (θ j)).left (e (θ j) (u (θ j))))
        ((Q (θ j)).right (k (θ j) zK))) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun j => ε (θ j) + dist (z (θ j)).val z₀) (fun _ => dist_nonneg)
    · intro j
      have htri := dist_triangle
        ((Q (θ j)).left (e (θ j) (u (θ j))))
        ((Q (θ j)).right (k (θ j) (z (θ j))))
        ((Q (θ j)).right (k (θ j) zK))
      have hiso := (Q (θ j)).right_isometry.dist_eq
        (k (θ j) (z (θ j))) (k (θ j) zK)
      change dist ((Q (θ j)).right (k (θ j) (z (θ j))))
        ((Q (θ j)).right (k (θ j) zK)) = dist (z (θ j)).val z₀ at hiso
      rw [hiso] at htri
      exact htri.trans (add_le_add (hcross (θ j)).le le_rfl)
    · simpa only [Function.comp_def, add_zero] using (hε.comp hθ).add hzdist
  have hvCross : Tendsto
      (fun j => dist ((Q (θ j)).left (e (θ j) (v (θ j))))
        ((Q (θ j)).right (k (θ j) y₀))) atTop (𝓝 0) := by
    exact squeeze_zero (fun _ => dist_nonneg) (fun j => (href (θ j)).le) (hε.comp hθ)
  have hdistlim : Tendsto (fun j => dist (v (θ j)).val (u (θ j)).val)
      atTop (𝓝 (dist y₀.val z₀)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (g := fun j =>
      dist ((Q (θ j)).left (e (θ j) (v (θ j)))) ((Q (θ j)).right (k (θ j) y₀)) +
      dist ((Q (θ j)).left (e (θ j) (u (θ j)))) ((Q (θ j)).right (k (θ j) zK)))
      (fun _ => dist_nonneg)
    · intro j
      have h := dist_dist_dist_le
        ((Q (θ j)).left (e (θ j) (v (θ j))))
        ((Q (θ j)).left (e (θ j) (u (θ j))))
        ((Q (θ j)).right (k (θ j) y₀))
        ((Q (θ j)).right (k (θ j) zK))
      have hleft := (Q (θ j)).left_isometry.dist_eq
        (e (θ j) (v (θ j))) (e (θ j) (u (θ j)))
      have hright := (Q (θ j)).right_isometry.dist_eq (k (θ j) y₀) (k (θ j) zK)
      change dist ((Q (θ j)).left (e (θ j) (v (θ j))))
        ((Q (θ j)).left (e (θ j) (u (θ j)))) =
          dist (v (θ j)).val (u (θ j)).val at hleft
      change dist ((Q (θ j)).right (k (θ j) y₀))
        ((Q (θ j)).right (k (θ j) zK)) = dist y₀.val z₀ at hright
      rwa [hleft, hright] at h
    · simpa only [add_zero] using hvCross.add huCross
  have hnearLimit : dist y₀.val z₀ ≤ ρ :=
    le_of_tendsto hdistlim (Eventually.of_forall (fun j => hnear (θ j)))
  have hconv := pointedGHConvergesUnbounded_rebase_of_expanding_realizations
    (fun j => hXgeo (θ j)) hYgeo
    (fun j => lt_of_le_of_lt hR (hs (θ j)))
    (fun j => lt_of_le_of_lt hR (ht (θ j)))
    (hsTop.comp hθ) (htTop.comp hθ)
    (fun j => Q (θ j)) (hQ.comp hθ)
    (fun j => e (θ j) (u (θ j))) (fun j => k (θ j) zK) z₀
    (Eventually.of_forall (fun _ => rfl)) huCross
  let : ∀ j, ProperSpace ((X (θ j)).rebase (e (θ j) (u (θ j))).val).carrier :=
    fun j => show ProperSpace (X (θ j)).carrier from inferInstance
  let : ProperSpace (Y.rebase z₀).carrier :=
    show ProperSpace Y.carrier from inferInstance
  have hascent : ∀ y : Y.carrier, 0 < dist z₀ y → dist z₀ y < b →
      HasLocalDistanceAscent c' z₀ y :=
    base_ascent_of_bad_radius_zero hconv hb hc hcc' (ha.comp hθ)
  have hhalf : b / 2 ≤ B z₀ := by
    apply hmax z₀ (b / 2) (by positivity) (by linarith)
    intro y hy hyb
    exact hascent y hy (by linarith)
  have heq : z₀ = y₀.val := by
    by_contra hne
    have hs' := hspire z₀ hz₀ hne
    rw [dist_comm] at hs'
    have hscale := mul_le_mul_of_nonneg_left hhalf hκ.le
    linarith only [hscale, hs', hnearLimit, hρb, _hρ]
  have hzero : Tendsto (fun j => dist (v (θ j)).val (u (θ j)).val) atTop (𝓝 0) := by
    simpa only [heq, dist_self] using hdistlim
  have hηle : η ≤ (0 : ℝ) :=
    ge_of_tendsto hzero (Eventually.of_forall (fun j => le_of_not_gt (hbad (ψ j))))
  exact (not_le_of_gt hη) hηle


end Poincare.CurvatureIntegral
