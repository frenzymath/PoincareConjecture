import PoincareConjecture.Proofs.M25.AppA_1_Necks.SmoothChainChart
import PoincareConjecture.Proofs.M25.AppA_1_Necks.OrderedChainCuts
import PoincareConjecture.Proofs.M25.Mathlib.FiberwiseUpperStretch
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem BalancedNeckChain.exists_finite_initial_carrier_chart :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (D : BalancedNeckChain g epsilon) {b : ℤ},
      D.shape = ChainShape.finite 0 b →
      epsilon ≤ epsilon0 →
      (∀ i ∈ D.shape.active, (D.neck i).IsSeparating) →
      ∃ Q : OpenPartialHomeomorph M M,
        Q.source = (⋃ i ∈ D.shape.active, (D.neck i).carrier) ∧
        Q.target = (D.neck 0).carrier ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ Q Q.source ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ Q.symm Q.target ∧
        EqOn (Q : M → M) id ((D.neck 0).region (-epsilon⁻¹) 0) ∧
        EqOn (Q.symm : M → M) id ((D.neck 0).region (-epsilon⁻¹) 0) := by
  classical
  obtain ⟨epsilon0, he0, hecap, hchart⟩ :=
    BalancedNeckChain.exists_smooth_chain_partial_chart.{u}
  refine ⟨epsilon0, he0, hecap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon D b hshape hsmall hsep
  have hb : (0 : ℤ) ≤ b := by
    obtain ⟨i, hi⟩ := D.active_nonempty
    rw [hshape] at hi
    change 0 ≤ i ∧ i ≤ b at hi
    exact hi.1.trans hi.2
  have hzero : (0 : ℤ) ∈ D.shape.active := by
    rw [hshape]
    exact ⟨le_rfl, hb⟩
  have hprev : (0 - 1 : ℤ) ∉ D.shape.active := by
    rw [hshape]
    change ¬ ((0 : ℤ) ≤ 0 - 1 ∧ 0 - 1 ≤ b)
    omega
  have hepos : 0 < epsilon :=
    D.epsilon_eq 0 hzero ▸ (D.neck 0).epsilon_pos
  let L : ℝ := epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr hepos
  let a : ℝ := 23 * L / 32
  let cut : ℝ := 25 * L / 32
  let U : Set M := ⋃ i ∈ D.shape.active, (D.neck i).carrier
  let q0 : ℤ → UnitTwoSphere := fun i =>
    ((D.neck i).coordinate_inverse (D.neck i).center).1
  let S : ℤ → ℝ → Set M := fun i t =>
    range (fun q : UnitTwoSphere => (D.neck i).coordinate_map (q, t))
  let negSide : ℤ → ℝ → Set M := fun i t =>
    connectedComponentIn (S i t)ᶜ
      ((D.neck i).coordinate_map (q0 i, (t - L) / 2))
  let posSide : ℤ → ℝ → Set M := fun i t =>
    connectedComponentIn (S i t)ᶜ
      ((D.neck i).coordinate_map (q0 i, (t + L) / 2))
  let W : ℤ → Set M := fun i => if i ∈ D.shape.active then
    ((D.neck i).carrier ∩
      (if i - 1 ∈ D.shape.active then posSide (i - 1) a else univ)) ∩
      (if i + 1 ∈ D.shape.active then negSide i cut else univ) else ∅
  obtain ⟨e, F, B, P, hF0, hB0, he, _, _, _, hupper, hbounds,
    hPsource, hPtarget, hP, hPi, hLocal⟩ := hchart D hsmall hsep 0 hzero
  obtain ⟨he0s, he0t, he0, hei0, heheight0, _, _⟩ := he 0 hzero
  change (e 0).source = univ ×ˢ Ioo (-L) L at he0s
  change P.source = U at hPsource
  let upper : UnitTwoSphere → ℝ := fun q => (F b ((B b).symm q, L)).2
  have huSmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ upper := by
    simpa only [hshape] using hupper
  have huBound (q : UnitTwoSphere) : L ≤ upper q := by
    simpa only [hshape] using (hbounds q).2
  have htarget : P.target =
      {z : RoundCylinderSpace | -L < z.2 ∧ z.2 < upper z.1} := by
    simpa only [hshape, hF0, hB0, Diffeomorph.symm_refl,
      Diffeomorph.coe_refl, id_eq] using hPtarget
  obtain ⟨G, _, _, _, hGfixInv, hGimage, hGpreimage⟩ :=
    Diffeomorph.exists_fiberwise_upper_stretch (I := 𝓡 2) L hL upper huSmooth huBound
  let R : OpenPartialHomeomorph M RoundCylinderSpace :=
    P.transHomeomorph G.symm.toHomeomorph
  have hRtarget : R.target = (e 0).source := by
    change (G : RoundCylinderSpace → RoundCylinderSpace) ⁻¹' P.target = (e 0).source
    rw [htarget, hGpreimage, he0s]
  let Q : OpenPartialHomeomorph M M := R.trans' (e 0) hRtarget
  have hQsource : Q.source = U := hPsource
  have hQtarget : Q.target = (D.neck 0).carrier := he0t
  have hR : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ R P.source :=
    G.symm.contMDiff.comp_contMDiffOn hP
  have hRmap : MapsTo R P.source (e 0).source := by
    intro x hx
    exact hRtarget ▸ R.map_source hx
  have hQ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Q Q.source :=
    he0.comp hR hRmap
  have hback : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun y => G ((e 0).symm y)) (e 0).target :=
    G.contMDiff.comp_contMDiffOn hei0
  have hbackmap : MapsTo (fun y => G ((e 0).symm y)) (e 0).target P.target := by
    intro y hy
    rw [htarget, ← hGimage]
    exact ⟨(e 0).symm y, he0s ▸ (e 0).map_target hy, rfl⟩
  have hQi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Q.symm Q.target :=
    hPi.comp hback hbackmap
  have hlocalZero : EqOn P (fun x => F 0 ((e 0).symm x)) (W 0) :=
    (hLocal 0).1
  have hcut : cut ∈ Ioo (-L) L := by
    dsimp only [cut]
    constructor <;> linarith only [hL]
  have hcutpos : 0 < cut := by
    dsimp only [cut]
    linarith only [hL]
  obtain ⟨H, _, hH, _, _, hSides, _⟩ := D.exists_ordered_saturated_heights hsep
  have hnegative : (D.neck 0).region (-L) 0 ⊆ W 0 := by
    intro x hx
    dsimp only [W]
    rw [if_pos hzero, if_neg hprev]
    refine ⟨⟨hx.1, mem_univ _⟩, ?_⟩
    split_ifs with hnext
    · have hside : negSide 0 cut =
          connectedComponent (D.neck 0).center ∩ (H 0) ⁻¹' Iio cut :=
        (hSides 0 hzero cut hcut).1
      rw [hside]
      refine ⟨(D.neck 0).m25_carrier_subset_connectedComponent hx.1, ?_⟩
      change H 0 x < cut
      rw [(hH 0 hzero).2.1 x hx.1]
      exact hx.2.2.trans hcutpos
    · exact mem_univ _
  have hPnegative (x : M) (hx : x ∈ (D.neck 0).region (-L) 0) :
      P x = (e 0).symm x := by
    simpa only [hF0, Diffeomorph.coe_refl, id_eq] using hlocalZero (hnegative hx)
  have hheightInverse (x : M) (hx : x ∈ (D.neck 0).carrier) :
      ((e 0).symm x).2 = ((D.neck 0).coordinate_inverse x).2 := by
    have hxt : x ∈ (e 0).target := he0t.symm ▸ hx
    have h := heheight0 ((e 0).symm x) ((e 0).map_target hxt)
    rw [(e 0).right_inv hxt] at h
    exact h.symm
  have hfix : EqOn (Q : M → M) id ((D.neck 0).region (-L) 0) := by
    intro x hx
    have hxt : x ∈ (e 0).target := he0t.symm ▸ hx.1
    have hs : ((e 0).symm x).2 < 0 := by
      rw [hheightInverse x hx.1]
      exact hx.2.2
    have hGx : G.symm ((e 0).symm x) = (e 0).symm x :=
      hGfixInv ⟨mem_univ _, hs.le⟩
    change e 0 (G.symm (P x)) = x
    rw [hPnegative x hx, hGx]
    exact (e 0).right_inv hxt
  have hfixInv : EqOn (Q.symm : M → M) id ((D.neck 0).region (-L) 0) := by
    intro x hx
    have hxs : x ∈ Q.source := by
      rw [hQsource]
      exact mem_iUnion₂.mpr ⟨0, hzero, hx.1⟩
    change Q.symm x = x
    calc
      Q.symm x = Q.symm (Q x) := congrArg Q.symm (hfix hx).symm
      _ = x := Q.left_inv hxs
  exact ⟨Q, hQsource, hQtarget, hQ, hQi, hfix, hfixInv⟩

end PoincareConjecture
