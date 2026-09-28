


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.ChartLevel.Transverse












set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]


def chartCircle (x : M) (r : ℝ) : Set M :=
  (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    sphere (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r


noncomputable def chartCircleSemicircle (x : M) (r : ℝ) (i : Fin 2) : ℝ → M :=
  (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ∘
    coordinateCircleArc (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r ((i : ℝ) * Real.pi)



def ChartCircleRegularAlong (x : M) (rx : ℝ) (y : M) (ry : ℝ) : Prop :=
  ∀ i : Fin 2,
    chartCircleSemicircle y ry i 0 ∉ chartCircle x rx ∧
    chartCircleSemicircle y ry i 1 ∉ chartCircle x rx ∧
    ∀ t ∈ Ioo (0 : ℝ) 1, chartCircleSemicircle y ry i t ∈ chartCircle x rx →
      deriv (fun u => ‖chartAt (EuclideanSpace ℝ (Fin 2)) x
        (chartCircleSemicircle y ry i u) - chartAt (EuclideanSpace ℝ (Fin 2)) x x‖ ^ 2) t ≠ 0

variable [T2Space M] [IsManifold (𝓡 2) ∞ M]



theorem exists_chart_circle_radii_general_position
    (s : Finset M) (R : M → ℝ) (hpos : ∀ x, 0 < R x)
    (hsub : ∀ x, closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (R x) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    ∃ ρ : M → ℝ, (∀ x ∈ s, ρ x ∈ Ioo (R x / 4) (R x / 3)) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        (chartCircle x (ρ x) ∩ chartCircle y (ρ y)).Finite) ∧
      (∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z →
        ∀ p ∈ chartCircle x (ρ x), p ∈ chartCircle y (ρ y) → p ∉ chartCircle z (ρ z)) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        ChartCircleRegularAlong x (ρ x) y (ρ y) ∨
          ChartCircleRegularAlong y (ρ y) x (ρ x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp, by simp, by simp⟩
  | @insert x s hx ih =>
      obtain ⟨ρ, hρ, hfinite, htriple, hregular⟩ := ih
      let V : Set M := ⋃ y : s, ⋃ z : s, ⋃ (_ : y ≠ z),
        chartCircle y (ρ y) ∩ chartCircle z (ρ z)
      have hV : V.Finite := finite_iUnion fun y => finite_iUnion fun z =>
        finite_iUnion fun hyz => hfinite y y.property z z.property
          (fun h => hyz (Subtype.ext h))
      have hedges (y : s) := exists_smoothEdges_of_chartCircle (M := M) y
        (chartAt (EuclideanSpace ℝ (Fin 2)) (y : M) (y : M))
        (show 0 < ρ y from (div_pos (hpos y) (by norm_num)).trans (hρ y y.property).1)
        (show sphere (chartAt (EuclideanSpace ℝ (Fin 2)) (y : M) (y : M)) (ρ y) ⊆
            (chartAt (EuclideanSpace ℝ (Fin 2)) (y : M)).target from
          sphere_subset_closedBall.trans ((closedBall_subset_closedBall
            (by linarith [(hρ y y.property).2, hpos y])).trans (hsub y)))
      choose edge hmap hinj hcover using hedges
      let edges : (s × Fin 2) → SmoothEdge M := fun i => edge i.1 i.2
      obtain ⟨a, ha, havoid, hinter⟩ := exists_chart_circle_transverse_edge_intersections
        x edges hV.toFinset (a := R x / 4) (b := R x / 3) (r := R x / 2) (R := R x)
        (div_pos (hpos x) (by norm_num)) (by linarith [hpos x])
        (by linarith [hpos x]) (by linarith [hpos x]) (hsub x)
      have hnew (y : s) : (chartCircle (y : M) (ρ y) ∩ chartCircle x a).Finite := by
        rw [show chartCircle (y : M) (ρ y) = ⋃ i, (edge y i).map '' Icc (0 : ℝ) 1 from
          (hcover y).symm, iUnion_inter]
        exact finite_iUnion (fun i => (hinter (y, i)).1)
      have hnewregular (y : s) : ChartCircleRegularAlong x a y (ρ y) := by
        intro i
        simpa only [edges, hmap y i, chartCircleSemicircle, chartCircle] using (hinter (y, i)).2
      have hnewavoid (y : M) (hy : y ∈ s) (z : M) (hz : z ∈ s) (hyz : y ≠ z)
          (p : M) (hpy : p ∈ chartCircle y (ρ y)) (hpz : p ∈ chartCircle z (ρ z)) :
          p ∉ chartCircle x a := by
        apply havoid p
        rw [Set.Finite.mem_toFinset]
        exact mem_iUnion.mpr ⟨⟨y, hy⟩, mem_iUnion.mpr ⟨⟨z, hz⟩,
          mem_iUnion.mpr ⟨fun h => hyz (congrArg Subtype.val h), hpy, hpz⟩⟩⟩
      refine ⟨Function.update ρ x a, ?_, ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · simpa using ha
        · have hyx : y ≠ x := fun h => hx (h ▸ hy)
          simpa [hyx] using hρ y hy
      · intro y hy z hz hyz
        rcases Finset.mem_insert.mp hy with rfl | hys
        · have hzs : z ∈ s := (Finset.mem_insert.mp hz).resolve_left (Ne.symm hyz)
          simpa [Ne.symm hyz, inter_comm] using hnew ⟨z, hzs⟩
        · have hyx : y ≠ x := fun h => hx (h ▸ hys)
          rcases Finset.mem_insert.mp hz with rfl | hzs
          · simpa [hyx] using hnew ⟨y, hys⟩
          · have hzx : z ≠ x := fun h => hx (h ▸ hzs)
            simpa [hyx, hzx] using hfinite y hys z hzs hyz
      · intro y hy z hz w hw hyz hyw hzw p hpy hpz hpw
        rcases Finset.mem_insert.mp hy with rfl | hys
        · have hzs : z ∈ s := (Finset.mem_insert.mp hz).resolve_left (Ne.symm hyz)
          have hws : w ∈ s := (Finset.mem_insert.mp hw).resolve_left (Ne.symm hyw)
          exact hnewavoid z hzs w hws hzw p (by simpa [Ne.symm hyz] using hpz)
            (by simpa [Ne.symm hyw] using hpw) (by simpa using hpy)
        · have hyx : y ≠ x := fun h => hx (h ▸ hys)
          rcases Finset.mem_insert.mp hz with rfl | hzs
          · have hws : w ∈ s := (Finset.mem_insert.mp hw).resolve_left (Ne.symm hzw)
            exact hnewavoid y hys w hws hyw p (by simpa [hyx] using hpy)
              (by simpa [Ne.symm hzw] using hpw) (by simpa using hpz)
          · have hzx : z ≠ x := fun h => hx (h ▸ hzs)
            rcases Finset.mem_insert.mp hw with rfl | hws
            · exact hnewavoid y hys z hzs hyz p (by simpa [hyx] using hpy)
                (by simpa [hzx] using hpz) (by simpa using hpw)
            · have hwx : w ≠ x := fun h => hx (h ▸ hws)
              exact htriple y hys z hzs w hws hyz hyw hzw p (by simpa [hyx] using hpy)
                (by simpa [hzx] using hpz) (by simpa [hwx] using hpw)
      · intro y hy z hz hyz
        rcases Finset.mem_insert.mp hy with rfl | hys
        · have hzs : z ∈ s := (Finset.mem_insert.mp hz).resolve_left (Ne.symm hyz)
          exact Or.inl (by simpa [Ne.symm hyz] using hnewregular ⟨z, hzs⟩)
        · have hyx : y ≠ x := fun h => hx (h ▸ hys)
          rcases Finset.mem_insert.mp hz with rfl | hzs
          · exact Or.inr (by simpa [hyx] using hnewregular ⟨y, hys⟩)
          · have hzx : z ≠ x := fun h => hx (h ▸ hzs)
            simpa [hyx, hzx] using hregular y hys z hzs hyz




theorem exists_finite_chart_ball_cover_general_position [CompactSpace M] :
    ∃ (s : Finset M) (r : M → ℝ),
      (∀ x ∈ s, 0 < r x) ∧
      (∀ x ∈ s, closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) ∧
      (⋃ x ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x)) = (univ : Set M) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        (chartCircle x (r x) ∩ chartCircle y (r y)).Finite) ∧
      (∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z →
        ∀ p ∈ chartCircle x (r x), p ∈ chartCircle y (r y) → p ∉ chartCircle z (r z)) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        ChartCircleRegularAlong x (r x) y (r y) ∨
          ChartCircleRegularAlong y (r y) x (r x)) := by
  obtain ⟨s, R, hpos, hsub, hcover⟩ := exists_finite_buffered_chart_ball_cover (M := M)
  obtain ⟨r, hr, hinter, htriple, hregular⟩ :=
    exists_chart_circle_radii_general_position s R hpos hsub
  refine ⟨s, r, ?_, ?_, ?_, hinter, htriple, hregular⟩
  · intro x hx
    exact (div_pos (hpos x) (by norm_num)).trans (hr x hx).1
  · intro x hx
    exact (closedBall_subset_closedBall (by linarith [(hr x hx).2, hpos x])).trans (hsub x)
  · apply Subset.antisymm (subset_univ _)
    rw [← hcover]
    intro y hy
    obtain ⟨x, hx, z, hz, rfl⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨x, hx,
      ⟨z, ball_subset_ball (hr x hx).1.le hz, rfl⟩⟩

end PoincareConjecture.Topology.Surface
