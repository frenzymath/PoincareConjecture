import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.Germ.InverseFunction
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CompactExtension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Angular
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Affine









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare

open PoincareConjecture

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)


theorem exists_smooth_height_retraction {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∃ σ : ℝ → ℝ,
      ContDiff ℝ ∞ σ ∧ (∀ t, |σ t| < R) ∧
      ∀ t, |t| < r → σ t = t := by
  let r := R / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : 2 * r < R := by dsimp [r]; linarith
  let b : ContDiffBump (0 : ℝ) := ⟨r, 2 * r, hr, by linarith⟩
  refine ⟨r, hr, by linarith, (fun t => t * b t), contDiff_id.mul b.contDiff, ?_, ?_⟩
  · intro t
    by_cases ht : |t| < 2 * r
    · have hle : |t * b t| ≤ |t| := by
        rw [abs_mul, abs_of_nonneg b.nonneg]
        nlinarith [b.le_one (x := t), abs_nonneg t]
      exact hle.trans_lt (ht.trans hrR)
    · have hb : b t = 0 := b.zero_of_le_dist
        (by simpa [Real.dist_eq] using le_of_not_gt ht)
      simpa only [hb, mul_zero, abs_zero] using hR
  · intro t ht
    have hb : b t = 1 := b.one_of_mem_closedBall
      (by simpa [Metric.mem_closedBall, Real.dist_eq] using ht.le)
    simp only [hb, mul_one]


theorem exists_angular_extension_of_fixing_zero
    (f : RoundCylinderSpace → RoundCylinderSpace)
    (hf : ContMDiff CylModel CylModel ∞ f)
    (hzero : ∀ q : UnitTwoSphere, f (q, 0) = (q, 0)) :
    ∃ r : ℝ, 0 < r ∧ ∃ D : Diffeomorph CylModel CylModel
        RoundCylinderSpace RoundCylinderSpace ∞,
      (∀ p, (D p).2 = p.2) ∧
      ∀ p : RoundCylinderSpace, |p.2| < r → (D p).1 = (f p).1 := by
  let : Nonempty UnitTwoSphere :=
    (NormedSpace.sphere_nonempty.mpr (zero_le_one : (0 : ℝ) ≤ 1)).coe_sort
  let : Nonempty RoundCylinderSpace := by
    change Nonempty (UnitTwoSphere × ℝ)
    infer_instance
  have hfa : ContMDiff CylModel (𝓡 2) ∞ (fun z : RoundCylinderSpace => (f z).1) :=
    contMDiff_fst.comp hf
  let A : RoundCylinderSpace → RoundCylinderSpace := fun p => ((f p).1, p.2)
  have hA : ContMDiff CylModel CylModel ∞ A :=
    (contMDiff_fst.comp hf).prodMk contMDiff_snd
  have hA0 (q : UnitTwoSphere) : A (q, 0) = (q, 0) := by simp [A, hzero]
  have hAlocal (q : UnitTwoSphere) : IsLocalDiffeomorphAt CylModel CylModel ∞ A (q, 0) := by
    let L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
        (EuclideanSpace ℝ (Fin 2) × ℝ) := mfderiv CylModel CylModel A (q, 0)
    have hL : L = (mfderiv CylModel (𝓡 2)
        (fun z : RoundCylinderSpace => (f z).1) (q, 0)).prod
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ) := by
      dsimp [L, A]
      rw [mfderiv_prodMk (hfa.mdifferentiableAt (by simp))
        mdifferentiableAt_snd, mfderiv_snd]
      rfl
    have hangular : (fun z : UnitTwoSphere => (f (z, 0)).1) = id :=
      funext fun z => congrArg Prod.fst (hzero z)
    have hinj : Function.Injective L := by
      intro v w hvw
      rw [hL] at hvw
      have h2 := congrArg Prod.snd hvw
      change v.2 = w.2 at h2
      have h1 := congrArg Prod.fst hvw
      change mfderiv CylModel (𝓡 2) (fun z : RoundCylinderSpace => (f z).1) (q, 0) v =
        mfderiv CylModel (𝓡 2) (fun z : RoundCylinderSpace => (f z).1) (q, 0) w at h1
      rw [mfderiv_prod_eq_add_apply (hfa.mdifferentiableAt (by simp)),
        mfderiv_prod_eq_add_apply (hfa.mdifferentiableAt (by simp)),
        h2, hangular, mfderiv_id] at h1
      exact Prod.ext (add_right_cancel h1) h2
    have hbij : Function.Bijective L :=
      ⟨hinj, (LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp hinj⟩
    let : ChartedSpace (EuclideanSpace ℝ (Fin 2) × ℝ) RoundCylinderSpace :=
      prodChartedSpace _ _ _ _
    let : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ RoundCylinderSpace := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) UnitTwoSphere ℝ
    have hh : ContMDiffOn CylModel CylModel ∞ A univ := hA.contMDiffOn
    change Function.Bijective (mfderiv CylModel CylModel A (q, 0)) at hbij
    rw [← modelWithCornersSelf_prod] at hh hbij ⊢
    exact isLocalDiffeomorphAt_of_contMDiffOn_bijective_mfderiv_modelSpace
      isOpen_univ hh (mem_univ _) hbij
  let K : Set RoundCylinderSpace := univ ×ˢ ({0} : Set ℝ)
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hKzero (p : RoundCylinderSpace) (hp : p ∈ K) : A p = p := by
    rcases p with ⟨q, t⟩
    have ht0 : t = 0 := hp.2
    subst t
    exact hA0 q
  have hKinj : InjOn A K := fun p hp q hq heq =>
    (hKzero p hp).symm.trans (heq.trans (hKzero q hq))
  obtain ⟨e, hKe, hKet, heq, he, hei⟩ :=
    exists_openPartialHomeomorph_of_injOn_compact hK hKinj (by
      rintro ⟨q, t⟩ ⟨_, ht⟩
      have ht0 : t = 0 := ht
      subst t
      exact hAlocal q)
  have hsource0 (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ e.source := hKe ⟨mem_univ _, rfl⟩
  have htarget0 (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ e.target := by
    apply hKet
    exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, hA0 q⟩
  obtain ⟨R, hR, hRe⟩ := CylinderGluing.exists_cylinder_collar
    ⟨e.source ∩ e.target, e.open_source.inter e.open_target⟩
    (fun q => ⟨hsource0 q, htarget0 q⟩)
  obtain ⟨r, hr, _, σ, hσ, hσbound, hσinner⟩ := exists_smooth_height_retraction hR
  have hes (q : UnitTwoSphere) (t : ℝ) : (q, σ t) ∈ e.source := (hRe _ (hσbound t)).1
  have het (q : UnitTwoSphere) (t : ℝ) : (q, σ t) ∈ e.target := (hRe _ (hσbound t)).2
  have hinvheight (q : UnitTwoSphere) (t : ℝ) : (e.symm (q, σ t)).2 = σ t := by
    have hh := congrArg Prod.snd (heq (e.map_target (het q t)))
    rw [e.right_inv (het q t)] at hh
    exact hh.symm
  let D (t : ℝ) : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞ := {
    toFun := fun q => (f (q, σ t)).1
    invFun := fun q => (e.symm (q, σ t)).1
    left_inv := by
      intro q
      have hh := congrArg Prod.fst (e.left_inv (hes q t))
      rw [heq (hes q t)] at hh
      exact hh
    right_inv := by
      intro q
      have hh := congrArg Prod.fst (e.right_inv (het q t))
      rw [heq (e.map_target (het q t))] at hh
      change (f (e.symm (q, σ t))).1 = q at hh
      have hp : ((e.symm (q, σ t)).1, σ t) = e.symm (q, σ t) :=
        Prod.ext rfl (hinvheight q t).symm
      change (f ((e.symm (q, σ t)).1, σ t)).1 = q
      rw [hp]
      exact hh
    contMDiff_toFun := contMDiff_fst.comp
      (hf.comp (contMDiff_id.prodMk contMDiff_const))
    contMDiff_invFun := by
      intro q
      exact contMDiffAt_fst.comp q
        ((hei.contMDiffAt (e.open_target.mem_nhds (het q t))).comp q
          (contMDiff_id.prodMk contMDiff_const).contMDiffAt) }
  obtain ⟨F, hF⟩ := CylinderGluing.exists_fiber_diffeomorph D
    (contMDiff_fst.comp (hf.comp
      (contMDiff_fst.prodMk (hσ.contMDiff.comp contMDiff_snd))))
  refine ⟨r, hr, F, ?_, ?_⟩
  · intro p
    rw [hF]
  · intro p hp
    rw [hF]
    change (f (p.1, σ p.2)).1 = (f p).1
    rw [hσinner p.2 hp]

end Poincare
