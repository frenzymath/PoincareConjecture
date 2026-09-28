import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilySourceAtlas
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutSides
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

theorem FamilySourceAtlas.height_critical_iff
    {original : UnitTwoSphere × ℝ → E3}
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    {S : FamilyCutState P u r cut D m0 B Phi n psi}
    (A : FamilySourceAtlas original S)
    (horiginal : IsCollarEmbedding original)
    (i : Fin n) (p : UnitTwoSphere) (hp : p ∈ (A.chart i).source) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun x : UnitTwoSphere => ⟪(u : E3), psi i (x, 0)⟫_ℝ) p = 0 ↔
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun x : UnitTwoSphere => ⟪(u : E3), original (x, 0)⟫_ℝ)
        (A.chart i p) = 0 := by
  let ret := A.chart i
  let f : UnitTwoSphere → ℝ := fun x => ⟪(u : E3), original (x, 0)⟫_ℝ
  let g : UnitTwoSphere → ℝ := fun x => ⟪(u : E3), psi i (x, 0)⟫_ℝ
  change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) g p = 0 ↔
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (ret p) = 0
  have hret : ret.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨(A.chart_smooth i).mdifferentiableOn (by simp),
      (A.chart_inverse i).mdifferentiableOn (by simp)⟩
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    (InnerProductSpace.toDual ℝ E3 (u : E3)).contDiff.contMDiff.comp
      (collar_central_contMDiff original horiginal)
  have hnear : g =ᶠ[𝓝 p] f ∘ ret := by
    filter_upwards [ret.open_source.mem_nhds hp] with x hx
    change ⟪(u : E3), psi i (x, 0)⟫_ℝ =
      ⟪(u : E3), original (ret x, 0)⟫_ℝ
    have hcentral := A.collar_eq i x hx 0 (by norm_num)
    simpa only [mul_zero] using
      congrArg (fun v : E3 => ⟪(u : E3), v⟫_ℝ) hcentral
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
    have hvalue := congrArg (fun L : TangentSpace (𝓡 2) p →L[ℝ] ℝ => L w) heq
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (ret p)
      (mfderiv (𝓡 2) (𝓡 2) ret p w) = 0 at hvalue
    rw [hw] at hvalue
    exact hvalue
  · intro hfzero
    rw [hd]
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg
      (fun L : TangentSpace (𝓡 2) (ret p) →L[ℝ] ℝ =>
        L (mfderiv (𝓡 2) (𝓡 2) ret p v)) hfzero

theorem FamilySourceAtlas.morse_chart
    {original : UnitTwoSphere × ℝ → E3}
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    {S : FamilyCutState P u r cut D m0 B Phi n psi}
    (A : FamilySourceAtlas original S) (i : Fin n)
    (q : UnitTwoSphere) (hqTarget : q ∈ (A.chart i).target)
    (sigma tau : ℝ)
    (oldChart : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (hsigma : sigma * sigma = 1) (htau : tau * tau = 1)
    (hq : q ∈ oldChart.source) (hcenter : oldChart q = 0)
    (hforward : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞
      oldChart oldChart.source)
    (hinverse : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞
      oldChart.symm oldChart.target)
    (hform : ∀ x ∈ oldChart.source,
      ⟪(u : E3), original (x, 0)⟫_ℝ =
        ⟪(u : E3), original (q, 0)⟫_ℝ +
          sigma * (oldChart x).1 ^ 2 + tau * (oldChart x).2 ^ 2) :
    let ret := A.chart i
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
      psi i (p, 0) = original (q, 0) ∧
      ∀ x ∈ e.source,
        ⟪(u : E3), psi i (x, 0)⟫_ℝ =
          ⟪(u : E3), psi i (p, 0)⟫_ℝ +
            sigma * (e x).1 ^ 2 + tau * (e x).2 ^ 2 := by
  let ret := A.chart i
  let p := ret.symm q
  let e := ret.trans oldChart
  have hcentral (x : UnitTwoSphere) (hx : x ∈ ret.source) :
      psi i (x, 0) = original (ret x, 0) := by
    simpa only [mul_zero] using A.collar_eq i x hx 0 (by norm_num)
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
    hforward.comp ((A.chart_smooth i).mono inter_subset_left) (fun _ hx => hx.2)
  have heiSmooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target :=
    (A.chart_inverse i).comp (hinverse.mono inter_subset_left) (fun _ hz => hz.2)
  have hcenterEq : psi i (p, 0) = original (q, 0) := by
    rw [hcentral p hpRet, hretp]
  refine ⟨OpenPartialHomeomorph.trans_source ret oldChart,
    OpenPartialHomeomorph.trans_target ret oldChart,
    (fun _ => rfl), (fun _ => rfl), hsigma, htau,
    hp, hecenter, hzTarget, hinvcenter, heSmooth, heiSmooth, hcenterEq, ?_⟩
  intro x hx
  have hold := hform (ret x) hx.2
  change ⟪(u : E3), psi i (x, 0)⟫_ℝ =
    ⟪(u : E3), psi i (p, 0)⟫_ℝ +
      sigma * (oldChart (ret x)).1 ^ 2 + tau * (oldChart (ret x)).2 ^ 2
  rw [hcentral x hx.1, hcenterEq]
  exact hold

theorem FamilySourceAtlas.sourceCore_critical_subsingleton
    {original : UnitTwoSphere × ℝ → E3}
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    {S : FamilyCutState P u r cut D m0 B Phi n psi}
    (A : FamilySourceAtlas original S)
    (horiginal : IsCollarEmbedding original)
    (hcount : ∀ k : Fin r, S.count k = 0)
    (hdistinct : InjOn
      (fun q : UnitTwoSphere => ⟪(u : E3), original (q, 0)⟫_ℝ)
      {q : UnitTwoSphere | mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), original (p, 0)⟫_ℝ) q = 0})
    (hseparates : ∀ p : UnitTwoSphere,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun x : UnitTwoSphere => ⟪(u : E3), original (x, 0)⟫_ℝ) p = 0 →
      ∀ q : UnitTwoSphere,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun x : UnitTwoSphere => ⟪(u : E3), original (x, 0)⟫_ℝ) q = 0 →
        ⟪(u : E3), original (p, 0)⟫_ℝ < ⟪(u : E3), original (q, 0)⟫_ℝ →
          ∃ k : Fin r,
            ⟪(u : E3), original (p, 0)⟫_ℝ < cut k ∧
              cut k < ⟪(u : E3), original (q, 0)⟫_ℝ) :
    ∀ i : Fin n,
      (S.sourceCore i ∩ {q : UnitTwoSphere | mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q = 0}).Subsingleton := by
  intro i p hp q hq
  let ret := A.chart i
  have hpSource : p ∈ ret.source := A.core_subset_source i hp.1
  have hqSource : q ∈ ret.source := A.core_subset_source i hq.1
  have hpCrit := (A.height_critical_iff horiginal i p hpSource).mp hp.2
  have hqCrit := (A.height_critical_iff horiginal i q hqSource).mp hq.2
  have hheight (x : UnitTwoSphere) (hx : x ∈ ret.source) :
      ⟪(u : E3), psi i (x, 0)⟫_ℝ = ⟪(u : E3), original (ret x, 0)⟫_ℝ := by
    have hcentral := A.collar_eq i x hx 0 (by norm_num)
    simpa only [mul_zero] using
      congrArg (fun v : E3 => ⟪(u : E3), v⟫_ℝ) hcentral
  have heqHeight : ⟪(u : E3), original (ret p, 0)⟫_ℝ =
      ⟪(u : E3), original (ret q, 0)⟫_ℝ := by
    rcases lt_trichotomy ⟪(u : E3), original (ret p, 0)⟫_ℝ
      ⟪(u : E3), original (ret q, 0)⟫_ℝ with hlt | heq | hgt
    · obtain ⟨k, hkp, hkq⟩ := hseparates (ret p) hpCrit (ret q) hqCrit hlt
      rcases S.component_cut_side k (hcount k) i with habove | hbelow
      · have h := habove p
        rw [hheight p hpSource] at h
        exact False.elim ((lt_asymm hkp) h)
      · have h := hbelow q
        rw [hheight q hqSource] at h
        exact False.elim ((lt_asymm hkq) h)
    · exact heq
    · obtain ⟨k, hkq, hkp⟩ := hseparates (ret q) hqCrit (ret p) hpCrit hgt
      rcases S.component_cut_side k (hcount k) i with habove | hbelow
      · have h := habove q
        rw [hheight q hqSource] at h
        exact False.elim ((lt_asymm hkq) h)
      · have h := hbelow p
        rw [hheight p hpSource] at h
        exact False.elim ((lt_asymm hkp) h)
  exact ret.injOn hpSource hqSource (hdistinct hpCrit hqCrit heqHeight)

end PoincareConjecture.M25.Topology3D
