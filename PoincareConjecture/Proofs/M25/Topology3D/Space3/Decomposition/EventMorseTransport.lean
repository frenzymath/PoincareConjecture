import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryEventRegions
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurfaceMorse
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

theorem RegularSurgeryEvent.retained_central_eq
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (i : Fin 2)
    (p : UnitTwoSphere) (hp : p ∈ (E.retainedChart i).source) :
    E.child i (p, 0) = parent ((E.retainedChart i) p, 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hret⟩ := E.retained_spec i
  simpa only [mul_zero] using hret p hp 0 (by norm_num)

theorem RegularSurgeryEvent.exists_unique_retained_disc_of_height_avoidance
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (q : UnitTwoSphere)
    (havoid : E.data.width ≤
      |⟪(u : E3), parent (q, 0)⟫_ℝ - E.cutHeight|) :
    ∃! i : Fin 2,
      q ∈ (![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i) ''
        closedBall (0 : E2) E.radius ∧
      q ∈ (E.retainedChart i).target := by
  let e : Fin 2 → OpenPartialHomeomorph E2 UnitTwoSphere :=
    ![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative]
  let K : Fin 2 → Set UnitTwoSphere := fun i => e i '' closedBall 0 E.radius
  let j : UnitTwoSphere → E3 := fun p => parent (p, 0)
  let core : Fin 2 → Set E3 := fun i => j '' K i
  let c := E.data.width / 2 * (1 - E.radius)
  let A := E.data.tube ''
    (sphere (0 : E2) 1 ×ˢ Ioo (E.cutHeight - c) (E.cutHeight + c))
  change ∃! i : Fin 2, q ∈ K i ∧ q ∈ (E.retainedChart i).target
  obtain ⟨hparent, _, hcores, _, _, _⟩ := E.region_identities
  change parent '' (univ ×ˢ ({0} : Set ℝ)) = core 0 ∪ core 1 ∪ A at hparent
  change Disjoint (core 0) (core 1) at hcores
  have hcwidth : c < E.data.width := by
    obtain ⟨_, _, hck, hkw, _, _⟩ := E.parameter_bounds
    exact hck.trans hkw
  have hcentral : Function.Injective j := by
    intro p p' hpp'
    exact congrArg Prod.fst (E.parent_embedding.2.1 (by simp) (by simp) hpp')
  have hnotA : j q ∉ A := by
    rintro ⟨⟨x, z⟩, ⟨_hx, hz⟩, heq⟩
    have hh : ⟪(u : E3), j q⟫_ℝ = z := by
      rw [← heq, E.data.tube_height]
    have hsmall : |⟪(u : E3), j q⟫_ℝ - E.cutHeight| < c := by
      rw [hh]
      exact abs_lt.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
    exact (not_lt_of_ge havoid) (hsmall.trans hcwidth)
  have hcover : j q ∈ core 0 ∪ core 1 ∪ A := by
    rw [← hparent]
    exact ⟨(q, 0), by simp, rfl⟩
  have howner : ∃ i : Fin 2, j q ∈ core i := by
    rcases hcover with (h0 | h1) | hA
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact False.elim (hnotA hA)
  obtain ⟨i, q', hq', heq⟩ := howner
  have hqK : q ∈ K i := (hcentral heq) ▸ hq'
  have hqTarget : q ∈ (E.retainedChart i).target := by
    obtain ⟨_, _, _, _, _, _, _, htarget, _, _, _⟩ := E.retained_spec i
    exact htarget hqK
  refine ⟨i, ⟨hqK, hqTarget⟩, ?_⟩
  intro k hk
  by_contra hki
  have hiCore : j q ∈ core i := ⟨q, hqK, rfl⟩
  have hkCore : j q ∈ core k := ⟨q, hk.1, rfl⟩
  fin_cases i <;> fin_cases k
  · exact hki rfl
  · exact disjoint_left.mp hcores hiCore hkCore
  · exact disjoint_left.mp hcores hkCore hiCore
  · exact hki rfl

theorem RegularSurgeryEvent.retained_height_critical_iff
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (i : Fin 2)
    (p : UnitTwoSphere) (hp : p ∈ (E.retainedChart i).source) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun x : UnitTwoSphere => ⟪(u : E3), E.child i (x, 0)⟫_ℝ) p = 0 ↔
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun x : UnitTwoSphere => ⟪(u : E3), parent (x, 0)⟫_ℝ)
        ((E.retainedChart i) p) = 0 := by
  let ret := E.retainedChart i
  let f : UnitTwoSphere → ℝ := fun x => ⟪(u : E3), parent (x, 0)⟫_ℝ
  let g : UnitTwoSphere → ℝ := fun x => ⟪(u : E3), E.child i (x, 0)⟫_ℝ
  change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) g p = 0 ↔
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (ret p) = 0
  obtain ⟨_, _, _, _, _, _, _, _, hsm, hsi, _⟩ := E.retained_spec i
  have hret : ret.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨hsm.mdifferentiableOn (by simp), hsi.mdifferentiableOn (by simp)⟩
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    (InnerProductSpace.toDual ℝ E3 (u : E3)).contDiff.contMDiff.comp
      (collar_central_contMDiff parent E.parent_embedding)
  have hnear : g =ᶠ[𝓝 p] f ∘ ret := by
    filter_upwards [ret.open_source.mem_nhds hp] with x hx
    change ⟪(u : E3), E.child i (x, 0)⟫_ℝ =
      ⟪(u : E3), parent (ret x, 0)⟫_ℝ
    rw [E.retained_central_eq i x hx]
  have hd : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) g p =
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (ret p)).comp
        (mfderiv (𝓡 2) (𝓡 2) ret p) := by
    rw [hnear.mfderiv_eq]
    exact mfderiv_comp p (hf.mdifferentiable (by simp) (ret p))
      (hret.mdifferentiableAt hp)
  constructor
  · intro hg
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := hret.mfderiv_surjective hp v
    have heq : (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (ret p)).comp
        (mfderiv (𝓡 2) (𝓡 2) ret p) = 0 := hd.symm.trans hg
    have hvalue := congrArg (fun A : TangentSpace (𝓡 2) p →L[ℝ] ℝ => A w) heq
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (ret p)
      (mfderiv (𝓡 2) (𝓡 2) ret p w) = 0 at hvalue
    rw [hw] at hvalue
    exact hvalue
  · intro hfzero
    rw [hd]
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg
      (fun A : TangentSpace (𝓡 2) (ret p) →L[ℝ] ℝ =>
        A (mfderiv (𝓡 2) (𝓡 2) ret p v)) hfzero

theorem RegularSurgeryEvent.retained_morse_chart
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (i : Fin 2)
    (q : UnitTwoSphere) (hqTarget : q ∈ (E.retainedChart i).target)
    (sigma tau : ℝ)
    (oldChart : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (hsigma : sigma * sigma = 1) (htau : tau * tau = 1)
    (hq : q ∈ oldChart.source) (hcenter : oldChart q = 0)
    (hforward : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞
      oldChart oldChart.source)
    (hinverse : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞
      oldChart.symm oldChart.target)
    (hform : ∀ x ∈ oldChart.source,
      ⟪(u : E3), parent (x, 0)⟫_ℝ =
        ⟪(u : E3), parent (q, 0)⟫_ℝ +
          sigma * (oldChart x).1 ^ 2 + tau * (oldChart x).2 ^ 2) :
    let ret := E.retainedChart i
    let p := ret.symm q
    let e := ret.trans oldChart
    e.source = ret.source ∩ ret ⁻¹' oldChart.source ∧
      e.target = oldChart.target ∩ oldChart.symm ⁻¹' ret.target ∧
      (∀ x : UnitTwoSphere, e x = oldChart (ret x)) ∧
      (∀ z : ℝ × ℝ, e.symm z = ret.symm (oldChart.symm z)) ∧
      sigma * sigma = 1 ∧ tau * tau = 1 ∧
      p ∈ e.source ∧ e p = 0 ∧ 0 ∈ e.target ∧ e.symm 0 = p ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target ∧
      E.child i (p, 0) = parent (q, 0) ∧
      ∀ x ∈ e.source,
        ⟪(u : E3), E.child i (x, 0)⟫_ℝ =
          ⟪(u : E3), E.child i (p, 0)⟫_ℝ +
            sigma * (e x).1 ^ 2 + tau * (e x).2 ^ 2 := by
  let ret := E.retainedChart i
  let p := ret.symm q
  let e := ret.trans oldChart
  obtain ⟨_, _, _, _, _, _, _, _, hretSmooth, hretInverse, _⟩ := E.retained_spec i
  have hpRet : p ∈ ret.source := ret.map_target hqTarget
  have hretp : ret p = q := ret.right_inv hqTarget
  have hp : p ∈ e.source := by
    change p ∈ ret.source ∧ ret p ∈ oldChart.source
    refine ⟨hpRet, ?_⟩
    rwa [hretp]
  have hecenter : e p = 0 := by
    change oldChart (ret p) = 0
    rw [hretp, hcenter]
  have hzTarget : (0 : ℝ × ℝ) ∈ e.target := by
    rw [← hecenter]
    exact e.map_source hp
  have hinvcenter : e.symm 0 = p := by
    rw [← hecenter]
    exact e.left_inv hp
  have heSmooth : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source :=
    hforward.comp (hretSmooth.mono inter_subset_left) (fun _ hx => hx.2)
  have heiSmooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target :=
    hretInverse.comp (hinverse.mono inter_subset_left) (fun _ hz => hz.2)
  have hcentral : E.child i (p, 0) = parent (q, 0) := by
    rw [E.retained_central_eq i p hpRet, hretp]
  refine ⟨OpenPartialHomeomorph.trans_source ret oldChart,
    OpenPartialHomeomorph.trans_target ret oldChart,
    (fun _ => rfl), (fun _ => rfl), hsigma, htau,
    hp, hecenter, hzTarget, hinvcenter, heSmooth, heiSmooth, hcentral, ?_⟩
  intro x hx
  have hold := hform (ret x) hx.2
  change ⟪(u : E3), E.child i (x, 0)⟫_ℝ =
    ⟪(u : E3), E.child i (p, 0)⟫_ℝ +
      sigma * (oldChart (ret x)).1 ^ 2 + tau * (oldChart (ret x)).2 ^ 2
  rw [E.retained_central_eq i x hx.1, hcentral]
  exact hold

end PoincareConjecture.M25.Topology3D
