import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.GoodTimes.CircleRelabeling

/-!
# Genuine angular convergence in the frozen C1 loop topology

Joint convergence of the actual angular values and bundled angular
velocities descends through the open angular parametrization. Compact
circle neighborhoods then give both compact-open components of the
frozen induced topology. Claim 19.28 and Remark 19.29, MT pp. 460-461;
M65 derivation 37.
-/

set_option autoImplicit false

open Set Filter Bundle
open scoped Topology ContDiff Manifold

namespace PoincareMT

private theorem continuousMap_tendsto_of_joint
    {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {l : Filter ι} (f : ι → C(X, Y)) (g : C(X, Y))
    (h : ∀ x, Tendsto (fun p : ι × X => f p.1 p.2) (l ×ˢ 𝓝 x) (𝓝 (g x))) :
    Tendsto f l (𝓝 g) := by
  rw [ContinuousMap.tendsto_nhds_compactOpen]
  intro K hK W hW hKW
  have hall : {p : ι × X | f p.1 p.2 ∈ W} ∈ l ×ˢ 𝓝ˢ K :=
    hK.mem_prod_nhdsSet_of_forall (fun x hx => (h x).eventually (hW.mem_nhds (hKW hx)))
  exact eventually_prod_principal_iff.mp
    ((Filter.prod_mono le_rfl principal_le_nhdsSet) hall)

private theorem circle_tendsto_of_angular
    {ι Y : Type*} [TopologicalSpace Y] {l : Filter ι}
    (f : ι → C(LoopCircle, Y)) (g : C(LoopCircle, Y))
    (h : ∀ x, Tendsto (fun p : ι × ℝ =>
      f p.1 ⟨Proofs.M58.angularPoint p.2, Proofs.M58.norm_angularPoint p.2⟩)
      (l ×ˢ 𝓝 x) (𝓝 (g ⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩))) :
    Tendsto f l (𝓝 g) := by
  apply continuousMap_tendsto_of_joint f g
  intro z
  obtain ⟨x, rfl⟩ := m65AngularCircle_surjective z
  rw [← m65AngularCircle_map_nhds x, Filter.prod_map_right, tendsto_map'_iff]
  exact h x

/-- Joint convergence of the genuine angular values and their actual
tangent-bundle velocities gives convergence in the contract's C1
loop space. Changing tangent base points are retained throughout.
Claim 19.28 and Remark 19.29, MT pp. 460-461; derivation 37. -/
theorem m65C1Loop_tendsto_of_angular
    {ι M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {l : Filter ι}
    (loops : ι → C1FreeLoopSpace (M := M)) (gamma : C1FreeLoopSpace (M := M))
    (hvalue : ∀ x, Tendsto (fun p : ι × ℝ => periodicFreeLoop (loops p.1) p.2)
      (l ×ˢ 𝓝 x) (𝓝 (periodicFreeLoop gamma x)))
    (htangent : ∀ x, Tendsto (fun p : ι × ℝ =>
      (⟨periodicFreeLoop (loops p.1) p.2, curveVelocity (periodicFreeLoop (loops p.1)) p.2⟩ :
        TangentBundle (𝓡 3) M)) (l ×ˢ 𝓝 x)
      (𝓝 (⟨periodicFreeLoop gamma x, curveVelocity (periodicFreeLoop gamma) x⟩ :
        TangentBundle (𝓡 3) M))) :
    Tendsto loops l (𝓝 gamma) := by
  let values (c : C1FreeLoopSpace (M := M)) : C(LoopCircle, M) := ⟨c.toFun, c.continuous⟩
  have heq (c : C1FreeLoopSpace (M := M)) (x : ℝ) : periodicFreeLoop c x =
      values c ⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩ :=
    c.boundary ⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩
  have hv : Tendsto (fun i => values (loops i)) l (𝓝 (values gamma)) := by
    apply circle_tendsto_of_angular
    intro x
    simpa only [heq] using hvalue x
  have ht : Tendsto (fun i => c1LoopTangent (loops i)) l (𝓝 (c1LoopTangent gamma)) := by
    apply circle_tendsto_of_angular
    intro x
    simpa only [m65PeriodicLoopTangent_eq] using htangent x
  have hi : Topology.IsInducing (fun c : C1FreeLoopSpace (M := M) =>
      (values c, c1LoopTangent c)) := ⟨rfl⟩
  exact hi.tendsto_nhds_iff.mpr (hv.prodMk_nhds ht)

end PoincareMT
