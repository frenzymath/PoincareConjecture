import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.OriginalRimTraversal
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.OriginalResolutionWordPaths
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.OriginalOldEndPaths
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.SquareRimReparametrization



set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1


def MarkedPLIntervalPath.sourcePath
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {F : Set X} {f : E → X} {W : Set E} {a b : E}
    (p : MarkedPLIntervalPath F f W a b) : Path a b where
  toFun t := p.chart t
  continuous_toFun := continuous_subtype_val.comp p.chart.continuous
  source' := p.chart_zero
  target' := p.chart_one


theorem path_trans_target_values
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {F : Set X}
    (f : E → X) {x y z : E} {u v w : F}
    (p : Path x y) (q : Path y z) (a : Path u v) (b : Path v w)
    (ha : ∀ t, (a t : X) = f (p t)) (hb : ∀ t, (b t : X) = f (q t)) :
    ∀ t, (a.trans b t : X) = f (p.trans q t) := by
  intro t
  simp only [Path.trans_apply]
  split_ifs
  · exact ha _
  · exact hb _



theorem original_square_rim_excluded_of_values
    {X : Type*} [TopologicalSpace X] {F : Set X}
    {base : F} {J : Subgroup (FundamentalGroup F base)} [J.Normal]
    (f : V2 → X) (rim : C(Q2, F))
    (hboundary : ∀ x : Q2, f x = (rim x : X))
    (basepath : Path base (rim squareRimBase))
    (hout : basepath.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ J)
    (H : Q2 ≃ₜ Q2)
    {x : F} (rho : Path x x)
    (hrho : ∀ t, (rho t : X) = f (H (squareRimLoop t)))
    (p : Path base x) : p.whiskeredLoopClass rho ∉ J := by
  have hx : rim (H squareRimBase) = x := by
    apply Subtype.ext
    exact (hboundary _).symm.trans (by simpa using (hrho 0).symm)
  have he : ((squareRimLoop.map H.continuous).map rim.continuous) =
      rho.cast hx hx := by
    apply Path.ext
    funext t
    apply Subtype.ext
    exact (hboundary _).symm.trans (hrho t).symm
  have hnew := squareRimLoop_homeomorph_excluded H rim J basepath (p.cast rfl hx) hout
  rw [he] at hnew
  exact hnew



theorem original_square_rim_nonempty_whisker
    {X : Type*} [TopologicalSpace X] {F : Set X} {base : F}
    (f : V2 → X) (rim : C(Q2, F))
    (hboundary : ∀ x : Q2, f x = (rim x : X))
    (basepath : Path base (rim squareRimBase)) (H : Q2 ≃ₜ Q2)
    {x : F} (rho : Path x x)
    (hrho : ∀ t, (rho t : X) = f (H (squareRimLoop t))) :
    Nonempty (Path base x) := by
  let : PathConnectedSpace UnitCircle :=
    unitCircleExp_surjective.pathConnectedSpace contMDiff_unitCircleExp.continuous
  let : PathConnectedSpace Q2 :=
    squareRimUnitCircle.symm.surjective.pathConnectedSpace squareRimUnitCircle.symm.continuous
  have hx : x = rim (H squareRimBase) := by
    apply Subtype.ext
    have hr : (x : X) = f (H squareRimBase) := by simpa using hrho 0
    exact hr.trans (hboundary _)
  exact ⟨(basepath.trans
    ((PathConnectedSpace.somePath squareRimBase (H squareRimBase)).map rim.continuous)).cast
      rfl hx⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
