import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.Mathlib.CollarInteriorLoops

set_option autoImplicit false
open Set

namespace Poincare.Topology

theorem fundamentalGroup_map_injective_of_surjective_kernel_control
    {Z X Y : Type*} [TopologicalSpace Z] [TopologicalSpace X] [TopologicalSpace Y]
    (i : C(Z, X)) (f : C(X, Y)) (x : Z)
    (hsur : Function.Surjective (FundamentalGroup.map i x))
    (hkernel : ∀ gamma : FundamentalGroup Z x,
      FundamentalGroup.map (f.comp i) x gamma = 1 → FundamentalGroup.map i x gamma = 1) :
    Function.Injective (FundamentalGroup.map f (i x)) := by
  apply (injective_iff_map_eq_one (FundamentalGroup.map f (i x))).mpr
  intro alpha halpha
  obtain ⟨gamma, rfl⟩ := hsur alpha
  apply hkernel gamma
  simpa only [FundamentalGroup.map_comp, MonoidHom.comp_apply] using halpha

theorem fundamentalGroup_map_injective_of_path
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x y : X} (p : Path x y)
    (hy : Function.Injective (FundamentalGroup.map f y)) :
    Function.Injective (FundamentalGroup.map f x) := by
  apply (injective_iff_map_eq_one (FundamentalGroup.map f x)).mpr
  intro gamma hgamma
  let c := Path.Homotopic.Quotient.mk p
  let eta : FundamentalGroup X y := c.symm.trans (gamma.trans c)
  have hmap : FundamentalGroup.map f y eta = 1 := by
    change Path.Homotopic.Quotient.map gamma f = Path.Homotopic.Quotient.refl (f x) at hgamma
    change (c.symm.trans (gamma.trans c)).map f = Path.Homotopic.Quotient.refl (f y)
    rw [Path.Homotopic.Quotient.map_trans, Path.Homotopic.Quotient.map_symm,
      Path.Homotopic.Quotient.map_trans, hgamma,
      Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.symm_trans]
  have heta := (injective_iff_map_eq_one (FundamentalGroup.map f y)).mp hy eta hmap
  have h := congrArg (fun q : FundamentalGroup X y => c.trans (q.trans c.symm)) heta
  change c.trans ((c.symm.trans (gamma.trans c)).trans c.symm) =
    c.trans ((Path.Homotopic.Quotient.refl y).trans c.symm) at h
  change (gamma : Path.Homotopic.Quotient x x) = Path.Homotopic.Quotient.refl x
  simpa only [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_symm_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.refl_trans] using h

theorem fundamentalGroup_map_injective_of_collar_kernel_control
    {E X Y : Type*} [TopologicalSpace E] [Zero E]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X) (hc : ContinuousOn c (K ×ˢ Icc (0 : ℝ) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (0 : ℝ) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ico (0 : ℝ) r)))
    (f : C(X, Y))
    (hkernel : ∀ (x : ↥((c '' (K ×ˢ ({0} : Set ℝ)))ᶜ))
      (gamma : FundamentalGroup ↥((c '' (K ×ˢ ({0} : Set ℝ)))ᶜ) x),
      FundamentalGroup.map
        (f.comp (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥((c '' (K ×ˢ ({0} : Set ℝ)))ᶜ), X))) x gamma = 1 →
      FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥((c '' (K ×ˢ ({0} : Set ℝ)))ᶜ), X)) x gamma = 1) :
    ∀ x : X, Function.Injective (FundamentalGroup.map f x) := by
  let U := (c '' (K ×ˢ ({0} : Set ℝ)))ᶜ
  let i : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hoff (x : U) : Function.Injective (FundamentalGroup.map f (x : X)) :=
    fundamentalGroup_map_injective_of_surjective_kernel_control i f x
      (fundamentalGroup_collar_rim_complement_surjective hK hr c hc hi ho x) (hkernel x)
  intro x
  by_cases hx : x ∈ c '' (K ×ˢ ({0} : Set ℝ))
  · obtain ⟨⟨a, t⟩, ⟨ha, ht⟩, rfl⟩ := hx
    have ht0 : t = 0 := ht
    subst t
    have hmid : (a, r / 2) ∈ K ×ˢ Icc (0 : ℝ) r := ⟨ha, by constructor <;> linarith⟩
    have havoid : c (a, r / 2) ∈ U := by
      rintro ⟨z, hz, hzeq⟩
      have hz0 : z.2 = 0 := hz.2
      have hzP : z ∈ K ×ˢ Icc (0 : ℝ) r :=
        ⟨hz.1, by rw [hz0]; exact ⟨le_rfl, hr.le⟩⟩
      have heq := congrArg (fun w : (K ×ˢ Icc (0 : ℝ) r : Set (E × ℝ)) => w.val.2)
        (hi.injective (show c (⟨z, hzP⟩ : (K ×ˢ Icc (0 : ℝ) r : Set (E × ℝ))) =
          c (⟨(a, r / 2), hmid⟩ : (K ×ˢ Icc (0 : ℝ) r : Set (E × ℝ))) from hzeq))
      change z.2 = r / 2 at heq
      linarith
    let p : Path (c (a, 0)) (c (a, r / 2)) := {
      toFun := fun s => c (a, (s : ℝ) * (r / 2))
      continuous_toFun := hc.comp_continuous
        (continuous_const.prodMk (continuous_subtype_val.mul continuous_const)) (by
          intro s
          refine ⟨ha, ?_, ?_⟩
          · exact mul_nonneg s.property.1 (by linarith)
          · nlinarith [s.property.2])
      source' := by simp
      target' := by simp }
    exact fundamentalGroup_map_injective_of_path f p (hoff ⟨_, havoid⟩)
  · exact hoff ⟨x, hx⟩

end Poincare.Topology
