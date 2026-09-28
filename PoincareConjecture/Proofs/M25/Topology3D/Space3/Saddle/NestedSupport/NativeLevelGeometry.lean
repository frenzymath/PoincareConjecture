import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsFamily
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhoodNesting
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceUpperTube
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceHighRegularity
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceCollar
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularHorizontalTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HyperbolaDiscArcs
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue










set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D



private theorem saddle_nested_compact_no_bypass
    (Slo Shi Vlo Vhi Clo Chi B R : Set E3)
    (T : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
    (hShi : IsPreconnected Shi)
    (hdecomp : Slo = B ∪ R) (hBR : Disjoint B R)
    (hB : IsCompact B) (hR : IsCompact (R \ Vlo))
    (hCap : IsCompact (Shi ∩ Chi))
    (hNonempty : (Shi ∩ Chi).Nonempty)
    (hVlo : Vlo ⊆ Clo) (hVhi : Vhi ⊆ Chi)
    (hBD : Disjoint B Clo)
    (hExterior : T '' (Slo \ Vlo) = Shi \ Vhi)
    (hRim : T '' (Slo ∩ (Clo \ Vlo)) = Shi ∩ (Chi \ Vhi)) :
    B = ∅ := by
  classical
  let P : Set E3 := T '' B
  let Q : Set E3 := (T '' (R \ Vlo)) ∪ (Shi ∩ Chi)
  have hP : IsCompact P := hB.image T.continuous
  have hQ : IsCompact Q := (hR.image T.continuous).union hCap
  have hBE : B ⊆ Slo \ Vlo := by
    intro x hx
    refine ⟨?_, fun hv => disjoint_left.mp hBD hx (hVlo hv)⟩
    rw [hdecomp]
    exact Or.inl hx
  have hPE : P ⊆ Shi \ Vhi := by
    rw [← hExterior]
    exact image_mono hBE
  have hPC : Disjoint P Chi := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hy
    have he := hPE ⟨x, hx, rfl⟩
    have hr : T x ∈ Shi ∩ (Chi \ Vhi) := ⟨he.1, hy, he.2⟩
    rw [← hRim] at hr
    obtain ⟨z, hz, hzx⟩ := hr
    have hzx' : z = x := T.injective hzx
    exact disjoint_left.mp hBD hx (hzx' ▸ hz.2.1)
  have hPQ : Disjoint P Q := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ (hr | hc)
    · obtain ⟨z, hz, hzx⟩ := hr
      have hzx' : z = x := T.injective hzx
      exact disjoint_left.mp hBR hx (hzx' ▸ hz.1)
    · exact disjoint_left.mp hPC ⟨x, hx, rfl⟩ hc.2
  have hcover : Shi ⊆ P ∪ Q := by
    intro y hy
    by_cases hc : y ∈ Chi
    · exact Or.inr (Or.inr ⟨hy, hc⟩)
    · have he : y ∈ Shi \ Vhi := ⟨hy, fun hv => hc (hVhi hv)⟩
      rw [← hExterior] at he
      obtain ⟨x, hx, rfl⟩ := he
      rw [hdecomp] at hx
      rcases hx.1 with hb | hr
      · exact Or.inl ⟨x, hb, rfl⟩
      · exact Or.inr (Or.inl ⟨x, ⟨hr, hx.2⟩, rfl⟩)
  have hShiQ : Shi ⊆ Q := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hShi)
        P Q hP.isClosed hQ.isClosed hcover
        (by rw [hPQ.inter_eq, inter_empty]) with hp | hq
    · obtain ⟨y, hy, hc⟩ := hNonempty
      exact False.elim (disjoint_left.mp hPC (hp hy) hc)
    · exact hq
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hp : T x ∈ P := ⟨x, hx, rfl⟩
  exact disjoint_left.mp hPQ hp (hShiQ (hPE hp).1)




theorem saddle_nested_reference_positive_level_connected :
    let U : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let g : ℝ → ℝ := fun w => (2 - 1 / w) * Real.sqrt (1 - w ^ 2)
    let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
    ∃ ws wm : ℝ,
      1 / 2 < ws ∧ ws < 3 / 4 ∧ g ws = 1 / 32 ∧
      0 < wm ∧ wm < 1 / 2 ∧ g wm = -(1 / 32) ∧
      let vs : E2 := !₂[-Real.sqrt (1 - ws ^ 2), 0]
      let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
      let k : ℝ := U vs
      let mu : ℝ := U vm
      ∀ d a : ℝ, k < a → a < mu →
        IsConnected ((nestedReferenceBallChart d).boundary ∩
          {y : E3 | H0 y = a + d}) := by
  classical
  dsimp only
  obtain ⟨ws, wm, hwslo, hwshi, hwsroot, hwmlo, hwmhi, hwmroot,
    rho, e0, e, c, _hvs, _hvm, _hklo, _hkhi, _hmulo, _hmax, _hunique,
    hrho, hsep, _hzero, _hbuffer, _htargetD, _he0, _he0i, _hquad0,
    _hfull, _hlower, _hrestrict, _hsource, _htarget, _hefun, _heinv,
    _he, _hei, _hquad, _hc, _hcrange, _hcid, _hwhole, htubes⟩ :=
      NestedReferenceLower.exists_upper_reference_tube
  refine ⟨ws, wm, hwslo, hwshi, hwsroot, hwmlo, hwmhi, hwmroot, ?_⟩
  intro d a hka hamu
  let U : E2 → ℝ := fun v =>
    ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let k : ℝ := U !₂[-Real.sqrt (1 - ws ^ 2), 0]
  let mu : ℝ := U !₂[Real.sqrt (1 - wm ^ 2), 0]
  let nu : ℝ := mu - rho ^ 2
  let deltaU : ℝ := rho ^ 2 / 8
  let S : Set E3 := (nestedReferenceBallChart d).boundary
  let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
  change k < a at hka
  change a < mu at hamu
  change k < mu - 9 * rho ^ 2 at hsep
  change IsConnected (S ∩ {y : E3 | H0 y = a + d})
  have hrho2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have hnu : k < nu ∧ nu < mu := by
    dsimp only [nu]
    constructor <;> linarith only [hsep, hrho2]
  have hdeltaU : 0 < deltaU := div_pos hrho2 (by norm_num)
  obtain ⟨T, _hr, _hrb, _hTf, _hTi, _hTs, _hTt, _hT, _hTinv,
    hTsource, _hTh, _hTih, hlevels⟩ := htubes d
  have hseed : IsConnected (S ∩ {y : E3 | H0 y = nu + d}) := by
    have hz : nu + d - d ∈ Icc (nu - deltaU / 2) (nu + deltaU / 2) := by
      constructor <;> linarith only [hdeltaU]
    have hh := (hlevels (nu + d) hz).2.2.2
    change T '' (sphere (0 : E2) 1 ×ˢ ({nu + d} : Set ℝ)) =
      S ∩ {y : E3 | H0 y = nu + d} at hh
    rw [← hh]
    have hdim : 1 < Module.rank ℝ E2 := by
      rw [← Module.finrank_eq_rank]
      norm_num [E2]
    exact ((isConnected_sphere hdim (0 : E2) zero_le_one).prod
      isConnected_singleton).image T (T.continuousOn.mono
        (fun p hp => hTsource ⟨sphere_subset_closedBall hp.1, mem_univ p.2⟩))
  let j : UnitTwoSphere → E3 := fun q => nestedReferenceDiffeomorph d (q : E3)
  let psi : UnitTwoSphere × ℝ → E3 := fun p =>
    nestedReferenceDiffeomorph d ((1 + p.2) • (p.1 : E3))
  have hpsi0 : (fun q : UnitTwoSphere => psi (q, 0)) = j := by
    funext q
    simp only [psi, j, add_zero, one_smul]
  obtain ⟨hpsi, hS, _, _⟩ := exists_nestedReference_collar d
  change IsCollarEmbedding psi at hpsi
  have hjS : range j = S := by
    simpa only [← hpsi0] using hS
  let u0 : UnitTwoSphere := ⟨EuclideanSpace.single (2 : Fin 3) 1, by simp⟩
  have hL : heightPlaneCoordinates u0 = heightCoordinates := by
    apply ContinuousLinearEquiv.ext
    funext y
    change heightCoordinates
      ((ℝ ∙ ((u0 : E3) - EuclideanSpace.single (2 : Fin 3) 1))ᗮ.reflection y) =
        heightCoordinates y
    rw [Submodule.reflection_mem_subspace_eq_self (by simp [u0])]
  have hheight : (fun q : UnitTwoSphere => ⟪(u0 : E3), psi (q, 0)⟫_ℝ) =
      fun q => H0 (j q) := by
    funext q
    rw [← heightPlaneCoordinates_snd u0, hL, congrFun hpsi0 q]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hband⟩ :=
    NestedReferenceLower.reference_high_sphere_regularity
      ws wm d hwslo hwshi hwsroot hwmlo hwmhi hwmroot
  have hreg (q : UnitTwoSphere)
      (hq : ⟪(u0 : E3), psi (q, 0)⟫_ℝ ∈ Icc (min a nu + d) (max a nu + d)) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u0 : E3), psi (p, 0)⟫_ℝ) q ≠ 0 := by
    rw [hheight]
    apply hband (min a nu) (max a nu)
      (Or.inr ⟨lt_min hka hnu.1, max_lt hamu hnu.2⟩) q
    change H0 (j q) ∈ Icc (min a nu + d) (max a nu + d)
    rw [← congrFun hheight q]
    exact hq
  obtain ⟨eta, _heta, hI, Phi, _hPhi, _hPhii, _, _, hPhiLevel⟩ :=
    exists_regular_collar_horizontal_transport psi hpsi u0
      (min a nu + d) (max a nu + d) (by gcongr; exact min_le_max) hreg
  simp only [hL, hpsi0, hjS] at hPhiLevel
  have haI : a + d ∈ Icc (min a nu + d) (max a nu + d) :=
    ⟨by linarith only [min_le_left a nu], by linarith only [le_max_left a nu]⟩
  have hnuI : nu + d ∈ Icc (min a nu + d) (max a nu + d) :=
    ⟨by linarith only [min_le_right a nu], by linarith only [le_max_right a nu]⟩
  let G : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
    (Phi (nu + d)).symm.trans (Phi (a + d))
  have hmem (x : E2) :
      heightCoordinates.symm (G x, a + d) ∈ S ↔
        heightCoordinates.symm (x, nu + d) ∈ S := by
    change heightCoordinates.symm
      (Phi (a + d) ((Phi (nu + d)).symm x), a + d) ∈ S ↔ _
    rw [hPhiLevel (a + d) (hI haI), ← hPhiLevel (nu + d) (hI hnuI),
      (Phi (nu + d)).apply_symm_apply]
  let F : E3 → E3 := fun y =>
    heightCoordinates.symm (G (heightCoordinates y).1, a + d)
  have hF : Continuous F := heightCoordinates.symm.continuous.comp
    ((G.continuous.comp heightCoordinates.continuous.fst).prodMk continuous_const)
  have himage : F '' (S ∩ {y : E3 | H0 y = nu + d}) =
      S ∩ {y : E3 | H0 y = a + d} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hcoord : heightCoordinates.symm ((heightCoordinates x).1, nu + d) = x := by
        rw [← hx.2]
        exact heightCoordinates.symm_apply_apply x
      refine ⟨(hmem _).mpr (hcoord.symm ▸ hx.1), ?_⟩
      change (heightCoordinates (heightCoordinates.symm _)).2 = a + d
      rw [heightCoordinates.apply_symm_apply]
    · intro hy
      let x : E3 := heightCoordinates.symm
        (G.symm (heightCoordinates y).1, nu + d)
      have hcoord : heightCoordinates.symm ((heightCoordinates y).1, a + d) = y := by
        rw [← hy.2]
        exact heightCoordinates.symm_apply_apply y
      have hxS : x ∈ S := by
        apply (hmem (G.symm (heightCoordinates y).1)).mp
        rw [G.apply_symm_apply, hcoord]
        exact hy.1
      refine ⟨x, ⟨hxS, ?_⟩, ?_⟩
      · change (heightCoordinates (heightCoordinates.symm _)).2 = nu + d
        rw [heightCoordinates.apply_symm_apply]
      · change heightCoordinates.symm
          (G (heightCoordinates (heightCoordinates.symm _)).1, a + d) = y
        rw [heightCoordinates.apply_symm_apply, G.apply_symm_apply, hcoord]
  rw [← himage]
  exact hseed.image F hF.continuousOn




theorem saddle_nested_reference_lower_connectors
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (k d rho delta sigma : ℝ)
    (hrho : 0 < rho) (hdelta : 0 < delta) (hsmall : delta < rho ^ 2)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hdisc : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} ⊆ e.target)
    (hheight : ∀ q ∈ e.source,
      (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2 =
        k + d - (e q).1 ^ 2 + (e q).2 ^ 2) :
    let f : UnitTwoSphere → ℝ := fun q =>
      (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2
    let m : ℝ × ℝ → UnitTwoSphere := fun s =>
      e.symm (sigma * s.2, sigma * s.1)
    let aa := Real.sqrt ((rho ^ 2 - delta) / 2)
    let bb := Real.sqrt ((rho ^ 2 + delta) / 2)
    let sg : Fin 2 → ℝ := ![1, -1]
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let vv : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
    let gamma : Fin 2 → unitInterval → UnitTwoSphere := fun i t =>
      m (sg i * vv t, sg i * Real.sqrt ((vv t) ^ 2 + delta))
    let p : Fin 4 → UnitTwoSphere := fun i => m (sx i * aa, sy i * bb)
    let Dc : Set UnitTwoSphere := e.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
    let V : Set UnitTwoSphere := e.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < rho ^ 2}
    let La : Set UnitTwoSphere := {q | f q = k + d - delta}
    (∀ i : Fin 2, Continuous (gamma i) ∧ Function.Injective (gamma i)) ∧
    Disjoint (range (gamma 0)) (range (gamma 1)) ∧
    (∀ i : Fin 2,
      gamma i 0 = p (finProdFinEquiv (i, (0 : Fin 2))) ∧
      gamma i 1 = p (finProdFinEquiv (i, (1 : Fin 2)))) ∧
    La ∩ Dc = ⋃ i : Fin 2, range (gamma i) ∧
    La ∩ V = ⋃ i : Fin 2, gamma i '' Ioo (0 : unitInterval) 1 := by
  classical
  let f : UnitTwoSphere → ℝ := fun q =>
    (heightCoordinates (nestedReferenceDiffeomorph d (q : E3))).2
  let r2 : ℝ × ℝ → ℝ := fun s => s.1 ^ 2 + s.2 ^ 2
  let Bc : Set (ℝ × ℝ) := {s | r2 s ≤ rho ^ 2}
  let Bo : Set (ℝ × ℝ) := {s | r2 s < rho ^ 2}
  let N : (ℝ × ℝ) → (ℝ × ℝ) := fun s => (sigma * s.2, sigma * s.1)
  let m : ℝ × ℝ → UnitTwoSphere := fun s => e.symm (N s)
  let Dc : Set UnitTwoSphere := e.symm '' Bc
  let V : Set UnitTwoSphere := e.symm '' Bo
  let La : Set UnitTwoSphere := {q | f q = k + d - delta}
  have hsigmaSq : sigma ^ 2 = 1 := by
    rcases hsigma with h | h <;> rw [h] <;> norm_num
  have hNinv (s : ℝ × ℝ) : N (N s) = s := by
    apply Prod.ext <;> dsimp only [N] <;>
      rw [← mul_assoc, ← pow_two, hsigmaSq, one_mul]
  have hNinj : Injective N := by
    intro s t hst
    exact (hNinv s).symm.trans ((congrArg N hst).trans (hNinv t))
  have hNcont : Continuous N := by dsimp only [N]; fun_prop
  have hNr (s : ℝ × ℝ) : r2 (N s) = r2 s := by
    dsimp only [r2, N]
    rw [mul_pow, mul_pow, hsigmaSq, one_mul, one_mul]
    ring
  have hBoBc : Bo ⊆ Bc := by
    intro s hs
    exact (show r2 s < rho ^ 2 from hs).le
  have hNs (s : ℝ × ℝ) (hs : s ∈ Bc) : N s ∈ e.target := by
    apply hdisc
    change r2 (N s) ≤ rho ^ 2
    rw [hNr]
    exact hs
  have hmcont : ContinuousOn m Bc :=
    e.symm.continuousOn.comp hNcont.continuousOn (fun s hs => hNs s hs)
  have hminj : InjOn m Bc := by
    intro s hs t ht hst
    exact hNinj (e.symm.injOn (hNs s hs) (hNs t ht) hst)
  have hmheight (s : ℝ × ℝ) (hs : s ∈ Bc) :
      f (m s) = k + d + (s.1 ^ 2 - s.2 ^ 2) := by
    have hh := hheight (m s) (e.map_target (hNs s hs))
    have heq : e (m s) = N s := e.right_inv (hNs s hs)
    change f (m s) = k + d - (e (m s)).1 ^ 2 + (e (m s)).2 ^ 2 at hh
    rw [heq] at hh
    change f (m s) = k + d - (sigma * s.2) ^ 2 + (sigma * s.1) ^ 2 at hh
    rw [mul_pow, mul_pow, hsigmaSq, one_mul, one_mul] at hh
    linarith only [hh]
  have hnormalize (Z : Set (ℝ × ℝ)) (hZ : ∀ s, s ∈ Z ↔ N s ∈ Z) :
      e.symm '' Z = m '' Z := by
    ext q
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨N s, (hZ s).mp hs, ?_⟩
      change e.symm (N (N s)) = e.symm s
      rw [hNinv]
    · rintro ⟨s, hs, rfl⟩
      exact ⟨N s, (hZ s).mp hs, rfl⟩
  have hDc : Dc = m '' Bc := hnormalize Bc (fun s => by
    change r2 s ≤ rho ^ 2 ↔ r2 (N s) ≤ rho ^ 2
    rw [hNr])
  have hV : V = m '' Bo := hnormalize Bo (fun s => by
    change r2 s < rho ^ 2 ↔ r2 (N s) < rho ^ 2
    rw [hNr])
  have hcut (Z : Set (ℝ × ℝ)) (hZ : Z ⊆ Bc) :
      La ∩ m '' Z =
        m '' {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧ s ∈ Z} := by
    ext q
    constructor
    · rintro ⟨hq, s, hs, rfl⟩
      refine ⟨s, ⟨?_, hs⟩, rfl⟩
      have hh := hmheight s (hZ hs)
      change f (m s) = k + d - delta at hq
      linarith only [hh, hq]
    · rintro ⟨s, ⟨ht, hs⟩, rfl⟩
      refine ⟨?_, ⟨s, hs, rfl⟩⟩
      change f (m s) = k + d - delta
      rw [hmheight s (hZ hs), ht]
      ring
  let aa := Real.sqrt ((rho ^ 2 - delta) / 2)
  let bb := Real.sqrt ((rho ^ 2 + delta) / 2)
  let sg : Fin 2 → ℝ := ![1, -1]
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let vv : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
  let lo : Fin 2 → unitInterval → ℝ × ℝ := fun i t =>
    (sg i * vv t, sg i * Real.sqrt ((vv t) ^ 2 + delta))
  let gamma : Fin 2 → unitInterval → UnitTwoSphere := fun i t => m (lo i t)
  let pm : Fin 4 → ℝ × ℝ := fun i => (sx i * aa, sy i * bb)
  let p : Fin 4 → UnitTwoSphere := fun i => m (pm i)
  obtain ⟨hlocal, hldis, hlclosed, hlopen, _, hends⟩ :=
    saddle_hyperbola_disc_arcs rho delta hrho hdelta hsmall
  have hlo (i : Fin 2) (t : unitInterval) :
      (lo i t).1 ^ 2 - (lo i t).2 ^ 2 = -delta ∧ lo i t ∈ Bc := by
    change lo i t ∈ {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
    rw [hlclosed]
    exact mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩
  have hgamma (i : Fin 2) : Continuous (gamma i) ∧ Injective (gamma i) := by
    refine ⟨hmcont.comp_continuous (hlocal i).1 (fun t => (hlo i t).2), ?_⟩
    intro s t hst
    exact (hlocal i).2.1 (hminj (hlo i s).2 (hlo i t).2 hst)
  have hgdis : Disjoint (range (gamma 0)) (range (gamma 1)) := by
    apply disjoint_left.mpr
    rintro q ⟨s, rfl⟩ ⟨t, ht⟩
    have heq : lo 1 t = lo 0 s := hminj (hlo 1 t).2 (hlo 0 s).2 ht
    exact disjoint_left.mp hldis ⟨s, rfl⟩ ⟨t, heq⟩
  have hgend (i : Fin 2) :
      gamma i 0 = p (finProdFinEquiv (i, (0 : Fin 2))) ∧
      gamma i 1 = p (finProdFinEquiv (i, (1 : Fin 2))) :=
    ⟨congrArg m (hends i).1, congrArg m (hends i).2.1⟩
  have hnegative : La ∩ Dc = ⋃ i : Fin 2, range (gamma i) := by
    have hh := hcut Bc (Subset.refl Bc)
    rw [← hDc] at hh
    change La ∩ Dc = m '' {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} at hh
    rw [hlclosed, image_iUnion] at hh
    apply hh.trans
    apply iUnion_congr
    intro i
    change m '' range (lo i) = range (m ∘ lo i)
    exact (Set.range_comp m (lo i)).symm
  have hnegativeOpen : La ∩ V = ⋃ i : Fin 2,
      gamma i '' Ioo (0 : unitInterval) 1 := by
    have hh := hcut Bo hBoBc
    rw [← hV] at hh
    change La ∩ V = m '' {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 < rho ^ 2} at hh
    rw [hlopen, image_iUnion] at hh
    simpa only [image_image] using hh
  exact ⟨hgamma, hgdis, hgend, hnegative, hnegativeOpen⟩




theorem saddle_nested_native_no_bypass
    (j : UnitTwoSphere → E3) (hj : Continuous j) (hji : Injective j)
    (H : E3 → ℝ) (hH : Continuous H)
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (c rho delta : ℝ) (hrho : 0 < rho) (hdelta : 0 < delta)
    (hsmall : delta < rho ^ 2)
    (hbuffer : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} ⊆ e.target)
    (heheight : ∀ q ∈ e.source, H (j q) = c - (e q).1 ^ 2 + (e q).2 ^ 2)
    (T : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) :
    let V : Set UnitTwoSphere := e.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < rho ^ 2}
    let C : Set UnitTwoSphere := e.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
    let La : Set UnitTwoSphere := {q | H (j q) = c - delta}
    let Lb : Set UnitTwoSphere := {q | H (j q) = c + delta}
    IsOpen V → IsCompact C → IsPreconnected (j '' Lb) →
    T '' (j '' (La \ V)) = j '' (Lb \ V) →
    T '' (j '' (La ∩ (C \ V))) = j '' (Lb ∩ (C \ V)) →
    ∀ B : Set UnitTwoSphere, B ⊆ La → IsCompact B →
      IsCompact (La \ B) → Disjoint B C → B = ∅ := by
  classical
  intro V C La Lb hV hC hConnected hExterior hRim B hBsub hB hRest hBC
  have hVC : V ⊆ C := image_mono (fun s hs =>
    (show s.1 ^ 2 + s.2 ^ 2 < rho ^ 2 from hs).le)
  have hsqrt : Real.sqrt delta < rho := (Real.sqrt_lt' hrho).mpr hsmall
  have hsrad : (0 : ℝ) ^ 2 + Real.sqrt delta ^ 2 ≤ rho ^ 2 := by
    nlinarith only [Real.lt_sq_of_sqrt_lt hsqrt, Real.sq_sqrt hdelta.le]
  have hstarget : ((0 : ℝ), Real.sqrt delta) ∈ e.target := hbuffer hsrad
  have hPoint : (Lb ∩ C).Nonempty := by
    refine ⟨e.symm (0, Real.sqrt delta), ?_, ⟨(0, Real.sqrt delta), hsrad, rfl⟩⟩
    change H (j (e.symm (0, Real.sqrt delta))) = c + delta
    rw [heheight _ (e.map_target hstarget), e.right_inv hstarget]
    simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sq_sqrt hdelta.le]
  have hLb : IsClosed Lb := isClosed_eq (hH.comp hj) continuous_const
  have hCap : IsCompact (j '' Lb ∩ j '' C) := by
    rw [← image_inter hji]
    exact (hC.inter_left hLb).image hj
  have hNonempty : (j '' Lb ∩ j '' C).Nonempty := by
    rw [← image_inter hji]
    exact hPoint.image j
  have hDecompSource : La = B ∪ (La \ B) := by
    ext q
    constructor
    · intro hq
      by_cases hb : q ∈ B
      · exact Or.inl hb
      · exact Or.inr ⟨hq, hb⟩
    · rintro (hb | hq)
      · exact hBsub hb
      · exact hq.1
  have hDecomp : j '' La = j '' B ∪ j '' (La \ B) := by
    conv_lhs => rw [hDecompSource, image_union]
  have hBR : Disjoint (j '' B) (j '' (La \ B)) :=
    disjoint_image_of_injective hji (disjoint_left.mpr (fun _ hb hr => hr.2 hb))
  have hRcompact : IsCompact (j '' (La \ B) \ j '' V) := by
    rw [← image_sdiff hji]
    exact (hRest.diff hV).image hj
  have hExterior' : T '' (j '' La \ j '' V) = j '' Lb \ j '' V := by
    simpa only [image_sdiff hji] using hExterior
  have hRim' : T '' (j '' La ∩ (j '' C \ j '' V)) =
      j '' Lb ∩ (j '' C \ j '' V) := by
    simpa only [image_inter hji, image_sdiff hji] using hRim
  have hEmpty : j '' B = ∅ :=
    saddle_nested_compact_no_bypass (j '' La) (j '' Lb) (j '' V) (j '' V)
      (j '' C) (j '' C) (j '' B) (j '' (La \ B)) T hConnected
      hDecomp hBR (hB.image hj) hRcompact hCap hNonempty
      (image_mono hVC) (image_mono hVC) (disjoint_image_of_injective hji hBC)
      hExterior' hRim'
  exact image_eq_empty.mp hEmpty

end PoincareConjecture.M25.Topology3D
