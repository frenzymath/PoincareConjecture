import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.SourceDiskNormalForm
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.Boundary.RectangleExtension

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

private theorem arc_coordinate_injective {cut a b x y : ℝ}
    (ha : cut < a) (hb : b < cut + p) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (heq : (x : C0) = (y : C0)) : x = y := by
  let J := AddCircle.openPartialHomeomorphCoe p cut
  have h := congrArg J.symm heq
  change J.symm (J x) = J.symm (J y) at h
  rwa [J.left_inv ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩,
    J.left_inv ⟨ha.trans_le hy.1, hy.2.trans_lt hb⟩] at h

theorem exists_hamiltonZero_source_disk_homeomorphic_normal_form
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (j : V2 → X0) (hj : PolyhedralPLInCharts e j D)
    {cut alpha beta cut' a b : ℝ}
    (halpha : cut < alpha) (hab : alpha < beta) (hbeta : beta < cut + p)
    (ha : cut' < a) (horder : a < b) (hb : b < cut' + p)
    (hfirst : ∀ z ∈ D, hamiltonZeroCircleMap phi (j z) ∈
      AddCircle.closedIntervalArc p alpha beta)
    (hsecond : ∀ z ∈ D, hamiltonZeroSecondCircleMap phi (j z) ∈
      AddCircle.closedIntervalArc p a b)
    (theta : C0) (hthird : ∀ z ∈ D, hamiltonZeroThirdCircleMap phi (j z) = theta)
    (hboundaryEdges : ∀ z ∈ Q,
      hamiltonZeroCircleMap phi (j z) ∈ ({(alpha : C0), (beta : C0)} : Set C0) ∨
      hamiltonZeroSecondCircleMap phi (j z) ∈ ({(a : C0), (b : C0)} : Set C0))
    (hinj : InjOn (fun z => hamiltonZeroAmbientMap phi (j z)) Q) :
    let u : C(D, X0) := ⟨fun z => hamiltonZeroAmbientMap phi (j z),
      (hamiltonZeroAmbientMap phi).continuous.comp hj.continuousOn.domRestrict⟩
    ∃ (v w : V2 → ℝ) (q : V2 → X0)
      (E : D ≃ₜ (Icc alpha beta ×ˢ Icc a b)),
      FinitePiecewiseAffineOn v D ∧ FinitePiecewiseAffineOn w D ∧ E.IsFinitePL ∧
      (∀ z : D, (E z : ℝ × ℝ) = (v z, w z)) ∧
      PolyhedralPLInCharts d q D ∧
      (∀ z ∈ D, Q0 (q z) = ((theta, (w z : C0)), (v z : C0))) ∧
      InjOn q D ∧ EqOn q (fun z => hamiltonZeroAmbientMap phi (j z)) Q ∧
      ∃ qD : C(D, X0), (∀ z : D, qD z = q z) ∧
      ∃ H : u.HomotopyRel qD {z : D | (z : V2) ∈ Q},
        ∀ t z, (Q0 (H (t, z))).1.1 = theta ∧
          (Q0 (H (t, z))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (H (t, z))).1.2 ∈ AddCircle.closedIntervalArc p a b := by
  intro u
  obtain ⟨v0, w0, q0, hv0, hw0, hrange0, hq0, hcoord0, hrim0,
      q0D, hq0D, Hinitial, hH0⟩ := exists_hamiltonZero_source_disk_rectangular_normal_form
    hd hphi j hj halpha hab.le hbeta ha horder.le hb hfirst hsecond theta hthird
  have hrealrim (z : V2) (hz : z ∈ Q) :
      (v0 z : C0) = hamiltonZeroCircleMap phi (j z) ∧
      (w0 z : C0) = hamiltonZeroSecondCircleMap phi (j z) := by
    have h := hcoord0 z (sphere_subset_closedBall hz)
    rw [hrim0 hz] at h
    exact ⟨(congrArg Prod.snd h).symm, (congrArg (fun x => x.1.2) h).symm⟩
  have hedges : ∀ z ∈ Q, v0 z ∈ ({alpha, beta} : Set ℝ) ∨
      w0 z ∈ ({a, b} : Set ℝ) := by
    intro z hz
    have hr := hrange0 z (sphere_subset_closedBall hz)
    have h := hboundaryEdges z hz
    rw [← (hrealrim z hz).1, ← (hrealrim z hz).2] at h
    simp only [mem_insert_iff, mem_singleton_iff] at h ⊢
    rcases h with (h | h) | (h | h)
    · exact Or.inl (Or.inl (arc_coordinate_injective halpha hbeta hr.1 ⟨le_rfl, hab.le⟩ h))
    · exact Or.inl (Or.inr (arc_coordinate_injective halpha hbeta hr.1 ⟨hab.le, le_rfl⟩ h))
    · exact Or.inr (Or.inl (arc_coordinate_injective ha hb hr.2 ⟨le_rfl, horder.le⟩ h))
    · exact Or.inr (Or.inr (arc_coordinate_injective ha hb hr.2 ⟨horder.le, le_rfl⟩ h))
  have hri : InjOn (fun z => (v0 z, w0 z)) Q := by
    intro x hx y hy hxy
    apply hinj hx hy
    rw [← hrim0 hx, ← hrim0 hy]
    apply (Q0).injective
    rw [hcoord0 x (sphere_subset_closedBall hx), hcoord0 y (sphere_subset_closedBall hy)]
    have hvxy : v0 x = v0 y := congrArg Prod.fst hxy
    have hwxy : w0 x = w0 y := congrArg Prod.snd hxy
    rw [hvxy, hwxy]
  obtain ⟨E, hE, hErim⟩ := exists_finitePL_rectangle_extension_of_injective_rim
    (fun z => (v0 z, w0 z)) (hv0.prod_mk hw0) hab horder
    (fun z hz => hrange0 z hz) hedges hri
  obtain ⟨r, hr, hEval⟩ := hE
  let v : V2 → ℝ := fun z => (r z).1
  let w : V2 → ℝ := fun z => (r z).2
  have hv : FinitePiecewiseAffineOn v D :=
    hr.postcomp (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  have hw : FinitePiecewiseAffineOn w D :=
    hr.postcomp (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  have hEv (z : D) : (E z : ℝ × ℝ) = (v z, w z) := hEval z
  have hrange (z : V2) (hz : z ∈ D) : v z ∈ Icc alpha beta ∧ w z ∈ Icc a b := by
    have h := (E ⟨z, hz⟩).property
    rwa [hEv] at h
  have hkeepv : EqOn v v0 Q := by
    intro z hz
    exact (congrArg Prod.fst ((hEv ⟨z, sphere_subset_closedBall hz⟩).symm.trans (hErim ⟨z, hz⟩)))
  have hkeepw : EqOn w w0 Q := by
    intro z hz
    exact (congrArg Prod.snd ((hEv ⟨z, sphere_subset_closedBall hz⟩).symm.trans (hErim ⟨z, hz⟩)))
  let thetaReal : ℝ := AddCircle.equivIco p 0 theta
  have htheta : (thetaReal : C0) = theta := AddCircle.coe_equivIco
  let q : V2 → X0 := fun z => (0, QuotientAddGroup.mk ![thetaReal, w z, v z])
  have hqcoord (z : V2) : Q0 (q z) = ((theta, (w z : C0)), (v z : C0)) := by
    change (((thetaReal : C0), (w z : C0)), (v z : C0)) = _
    rw [htheta]
  let linear : (ℝ × ℝ) →L[ℝ] V3 := ContinuousLinearMap.pi
    ![0, ContinuousLinearMap.snd ℝ ℝ ℝ, ContinuousLinearMap.fst ℝ ℝ ℝ]
  let lift : (ℝ × ℝ) →ᴬ[ℝ] ((Fin 0 ⊕ Fin 3) → ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 0) (Fin 3)
      (fun _ => ℝ)).symm.toContinuousAffineEquiv.toContinuousAffineMap.comp
      ((ContinuousAffineMap.const ℝ (ℝ × ℝ) (0 : Fin 0 → ℝ)).prod
        (linear.toContinuousAffineMap + ContinuousAffineMap.const ℝ (ℝ × ℝ) ![thetaReal, 0, 0]))
  have hq : PolyhedralPLInCharts d q D := by
    apply (hd.polyhedralPL_projection ((hv.prod_mk hw).postcomp lift)).congr
    intro z hz
    apply Prod.ext
    · rfl
    · apply congrArg QuotientAddGroup.mk
      funext i
      fin_cases i
      · change 0 + thetaReal = thetaReal
        exact zero_add _
      · change w z + 0 = w z
        exact add_zero _
      · change v z + 0 = v z
        exact add_zero _
  have hqi : InjOn q D := by
    intro x hx y hy hxy
    have hc := congrArg Q0 hxy
    rw [hqcoord, hqcoord] at hc
    have hvxy := arc_coordinate_injective halpha hbeta (hrange x hx).1 (hrange y hy).1
      (congrArg Prod.snd hc)
    have hwxy := arc_coordinate_injective ha hb (hrange x hx).2 (hrange y hy).2
      (congrArg (fun z => z.1.2) hc)
    apply congrArg Subtype.val (E.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) ?_)
    apply Subtype.ext
    rw [hEv, hEv, hvxy, hwxy]
  have hqbound : EqOn q (fun z => hamiltonZeroAmbientMap phi (j z)) Q := by
    intro z hz
    rw [← hrim0 hz]
    apply (Q0).injective
    rw [hqcoord, hcoord0 z (sphere_subset_closedBall hz), hkeepv hz, hkeepw hz]
  let vc : C(D, ℝ) := ⟨fun z => v z, hv.continuousOn.domRestrict⟩
  let wc : C(D, ℝ) := ⟨fun z => w z, hw.continuousOn.domRestrict⟩
  let v0c : C(D, ℝ) := ⟨fun z => v0 z, hv0.continuousOn.domRestrict⟩
  let w0c : C(D, ℝ) := ⟨fun z => w0 z, hw0.continuousOn.domRestrict⟩
  let qD : C(D, X0) := ⟨fun z => q z, hq.continuousOn.domRestrict⟩
  let mix (f g : C(D, ℝ)) : C(unitInterval × D, ℝ) :=
    ⟨fun z => (1 - (z.1 : ℝ)) * f z.2 + (z.1 : ℝ) * g z.2, by fun_prop⟩
  let G : C(unitInterval × D, X0) := ⟨fun z => (Q0).symm
    ((theta, ((mix w0c wc z : ℝ) : C0)), ((mix v0c vc z : ℝ) : C0)), by fun_prop⟩
  have hGcoord (t : unitInterval) (z : D) : Q0 (G (t, z)) =
      ((theta, ((mix w0c wc (t, z) : ℝ) : C0)), ((mix v0c vc (t, z) : ℝ) : C0)) :=
    (Q0).apply_symm_apply _
  let H1 : q0D.HomotopyRel qD {z : D | (z : V2) ∈ Q} := {
    toFun := G
    continuous_toFun := G.continuous
    map_zero_left := by
      intro z
      apply (Q0).injective
      rw [hGcoord, hq0D, hcoord0 z z.property]
      simp only [mix, ContinuousMap.coe_mk, Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
      rfl
    map_one_left := by
      intro z
      apply (Q0).injective
      rw [hGcoord]
      change _ = Q0 (q z)
      rw [hqcoord]
      simp only [mix, ContinuousMap.coe_mk, Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
      rfl
    prop' := by
      intro t z hz
      apply (Q0).injective
      change Q0 (G (t, z)) = Q0 (q0D z)
      rw [hGcoord, hq0D, hcoord0 z z.property]
      have hm (f g : C(D, ℝ)) (heq : g z = f z) : mix f g (t, z) = f z := by
        dsimp [mix]
        rw [heq]
        ring
      rw [hm w0c wc (hkeepw hz), hm v0c vc (hkeepv hz)]
      rfl }
  have hH1 (t : unitInterval) (z : D) : (Q0 (H1 (t, z))).1.1 = theta ∧
      (Q0 (H1 (t, z))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
      (Q0 (H1 (t, z))).1.2 ∈ AddCircle.closedIntervalArc p a b := by
    rw [show H1 (t, z) = G (t, z) from rfl, hGcoord]
    refine ⟨rfl, ⟨mix v0c vc (t, z), ?_, rfl⟩, ⟨mix w0c wc (t, z), ?_, rfl⟩⟩
    · exact (convex_Icc alpha beta) (hrange0 z z.property).1 (hrange z z.property).1
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
    · exact (convex_Icc a b) (hrange0 z z.property).2 (hrange z z.property).2
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  refine ⟨v, w, q, E, hv, hw, ⟨r, hr, hEval⟩, hEv, hq, fun z _ => hqcoord z,
    hqi, hqbound, qD, fun _ => rfl, Hinitial.trans H1, ?_⟩
  intro t z
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hH0 _ z
  · exact hH1 _ z

end PoincareConjecture.M76
