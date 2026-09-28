import Mathlib.Geometry.Manifold.Diffeomorph















open Set TopologicalSpace Topology
open scoped ContDiff Manifold

namespace Poincare

variable {E E' H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y]




theorem exists_diffeomorph_of_monotone_open_cover
    (U : ℕ → Opens X) (V : ℕ → Opens Y)
    (e : ∀ n, Diffeomorph I I' (U n) (V n) ∞)
    (hmono : Monotone U) (hcover : ∀ x, ∃ n, x ∈ U n)
    (hagree : ∀ (n m : ℕ) (x : U n) (y : U m),
      (x : X) = y → (e n x : Y) = e m y) :
    ∃ F : Diffeomorph I I' X ↥(⨆ n, V n) ∞,
      (∀ (n : ℕ) (x : U n), (F x : Y) = e n x) ∧
      (∀ (n : ℕ) (y : V n),
        F.symm ⟨y, Opens.mem_iSup.mpr ⟨n, y.property⟩⟩ = (e n).symm y) ∧
      range (fun x => (F x : Y)) = ⋃ n, (V n : Set Y) := by
  classical
  let W : Opens Y := ⨆ n, V n
  let f : X → Y := fun x => e (hcover x).choose ⟨x, (hcover x).choose_spec⟩
  have hf (n : ℕ) (x : U n) : f x = e n x := hagree _ n _ x rfl
  have hsmooth : ContMDiff I I' ∞ f := by
    intro x
    obtain ⟨n, hn⟩ := hcover x
    apply (contMDiffAt_subtype_iff (x := (⟨x, hn⟩ : U n))).mp
    have heq : (fun z : U n => f z) = (fun z => (e n z : Y)) := funext (hf n)
    rw [heq]
    exact (contMDiff_subtype_val.comp (e n).contMDiff).contMDiffAt
  have hinj : Function.Injective f := by
    intro x y h
    obtain ⟨n, hn⟩ := hcover x
    obtain ⟨m, hm⟩ := hcover y
    let x' : U (max n m) := ⟨x, hmono (le_max_left n m) hn⟩
    let y' : U (max n m) := ⟨y, hmono (le_max_right n m) hm⟩
    have heq : e (max n m) x' = e (max n m) y' := by
      apply Subtype.ext
      simpa only [← hf] using h
    exact congrArg Subtype.val ((e (max n m)).injective heq)
  have hrange : range f = (W : Set Y) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨n, hn⟩ := hcover x
      apply Opens.mem_iSup.mpr
      refine ⟨n, ?_⟩
      rw [hf n ⟨x, hn⟩]
      exact (e n ⟨x, hn⟩).property
    · intro hy
      obtain ⟨n, hn⟩ := Opens.mem_iSup.mp hy
      refine ⟨(e n).symm ⟨y, hn⟩, ?_⟩
      rw [hf]
      exact congrArg Subtype.val ((e n).apply_symm_apply ⟨y, hn⟩)
  let g : W → X := fun y =>
    let h := Opens.mem_iSup.mp y.property
    (e h.choose).symm ⟨y, h.choose_spec⟩
  have hfg (y : W) : f (g y) = y := by
    dsimp [g]
    rw [hf]
    exact congrArg Subtype.val ((e _).apply_symm_apply _)
  have hg (n : ℕ) (y : V n) :
      g ⟨y, Opens.mem_iSup.mpr ⟨n, y.property⟩⟩ = (e n).symm y := by
    apply hinj
    rw [hfg, hf]
    exact (congrArg Subtype.val ((e n).apply_symm_apply y)).symm
  have hgsmooth : ContMDiff I' I ∞ g := by
    intro y
    obtain ⟨n, hn⟩ := Opens.mem_iSup.mp y.property
    let P : Opens W :=
      ⟨{z | (z : Y) ∈ V n}, (V n).isOpen.preimage continuous_subtype_val⟩
    let y' : P := ⟨y, hn⟩
    apply (contMDiffAt_subtype_iff (x := y')).mp
    let localPoint : P → V n := fun z => ⟨z.1.1, z.property⟩
    have hlocal : ContMDiff I' I' ∞ localPoint := by
      rw [← ContMDiff.subtypeVal_comp_iff (V n)]
      change ContMDiff I' I' ∞ (fun z : P => (z.1.1 : Y))
      exact (contMDiff_subtype_val (U := W)).comp
        (contMDiff_subtype_val (U := P))
    have heq : (fun z : P => g z) =
        (fun z => ((e n).symm (localPoint z) : X)) := by
      funext z
      exact hg n (localPoint z)
    rw [heq]
    exact (contMDiff_subtype_val.comp ((e n).symm.contMDiff.comp hlocal)).contMDiffAt
  let F : Diffeomorph I I' X W ∞ :=
    { toFun := fun x => ⟨f x, hrange.subset (mem_range_self x)⟩
      invFun := g
      left_inv := fun _ => hinj (hfg _)
      right_inv := fun y => Subtype.ext (hfg y)
      contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff W _).mp hsmooth
      contMDiff_invFun := hgsmooth }
  exact ⟨F, hf, hg, hrange.trans (Opens.coe_iSup V)⟩

end Poincare
