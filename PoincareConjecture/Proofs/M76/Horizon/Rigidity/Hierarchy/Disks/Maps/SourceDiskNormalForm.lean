import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.OriginalCircleCoordinate
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Compression.SlabCoordinate
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.ThirdCoordinateLifts
import PoincareConjecture.Proofs.M76.Rigidity.OriginalCollarEndpointPL
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CollarCollapsePL
import PoincareConjecture.Proofs.M76.Rigidity.StandardHierarchyParameterPL
import PoincareConjecture.Proofs.M76.Mathlib.SupportedFinitePLExtension










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

private theorem finitePL_comp_on_open
    {E F G X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F} {f : E → X} {g : X → G}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hf : PolyhedralPLInCharts e f K.space) {U : Set X}
    (hmap : MapsTo f K.space U)
    (hg : ∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U)) :
    FinitePiecewiseAffineOn (g ∘ f) K.space := by
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  obtain ⟨i, J, V, _, hJK, hV, hxV, hVJ, hfJ, hcoords⟩ := hf.coordinates x
  have hcomp := (hg i).comp_finitePiecewiseAffineOn hcoords (by
    intro y hy
    refine ⟨(e i).mapsTo (hfJ hy), ?_⟩
    change (e i).symm (e i (f y)) ∈ U
    rw [(e i).left_inv (hfJ hy)]
    exact hmap (hJK hy))
  have hgf : FinitePiecewiseAffineOn (g ∘ f) J.space := hcomp.congr (by
    intro y hy
    exact congrArg g ((e i).left_inv (hfJ hy)))
  obtain ⟨N, hN, hNJ, hgfN⟩ := hgf
  exact ⟨N, V, hN, hV, hxV, fun y hy => hNJ.symm.subset (hVJ hy), hgfN⟩

private theorem finitePL_arc_coordinate
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph X0 V3) (q : C(X0, C0))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (j : E → X0) (hj : PolyhedralPLInCharts e j K.space)
    {cut a b : ℝ} (ha : cut < a) (hb : b < cut + p)
    (hrange : ∀ z ∈ K.space, q (j z) ∈ AddCircle.closedIntervalArc p a b)
    (hlocal : ∀ i, let A := AddCircle.openPartialHomeomorphCoe p cut
      LocallyPiecewiseAffineOn ((A.symm ∘ q) ∘ (e i).symm)
        ((e i).target ∩ (e i).symm ⁻¹' (q ⁻¹' A.target))) :
    ∃ w : E → ℝ, FinitePiecewiseAffineOn w K.space ∧
      (∀ z ∈ K.space, w z ∈ Icc a b) ∧
      ∀ z ∈ K.space, (w z : C0) = q (j z) := by
  let A := AddCircle.openPartialHomeomorphCoe p cut
  have hsource {t : ℝ} (ht : t ∈ Icc a b) : t ∈ A.source :=
    ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have htarget : MapsTo j K.space (q ⁻¹' A.target) := by
    intro z hz
    obtain ⟨t, ht, heq⟩ := hrange z hz
    change q (j z) ∈ A.target
    rw [← heq]
    exact A.map_source (hsource ht)
  refine ⟨(A.symm ∘ q) ∘ j, finitePL_comp_on_open K hK hj htarget hlocal, ?_, ?_⟩
  · intro z hz
    obtain ⟨t, ht, heq⟩ := hrange z hz
    change A.symm (q (j z)) ∈ Icc a b
    rw [← heq]
    change A.symm (A t) ∈ Icc a b
    rw [A.left_inv (hsource ht)]
    exact ht
  · intro z hz
    exact A.right_inv (htarget hz)

private theorem exists_bounded_scalar_boundary_extension
    (K B : SimplicialComplex ℝ V2) (hK : K.faces.Finite)
    (hBK : B.space ⊆ K.space) (w : V2 → ℝ)
    (hw : FinitePiecewiseAffineOn w B.space)
    {a b : ℝ} (hab : a ≤ b) (hrange : ∀ z ∈ B.space, w z ∈ Icc a b) :
    ∃ v : V2 → ℝ, FinitePiecewiseAffineOn v K.space ∧
      EqOn v w B.space ∧ ∀ z ∈ K.space, v z ∈ Icc a b := by
  obtain ⟨v, hv, hkeep, _, _⟩ := hw.exists_supported_extension K hK hBK isOpen_univ (subset_univ _)
  have hconst (t : ℝ) : FinitePiecewiseAffineOn (fun _ : V2 => t) K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine (ContinuousAffineMap.const ℝ V2 t)⟩
  refine ⟨fun z => max a (min b (v z)), (hconst a).max ((hconst b).min hv), ?_, ?_⟩
  · intro z hz
    change max a (min b (v z)) = w z
    rw [hkeep hz, min_eq_right (hrange z hz).2, max_eq_right (hrange z hz).1]
  · intro z hz
    exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩





theorem exists_hamiltonZero_source_disk_rectangular_normal_form
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (j : V2 → X0) (hj : PolyhedralPLInCharts e j D)
    {cut alpha beta cut' a b : ℝ}
    (halpha : cut < alpha) (hab : alpha ≤ beta) (hbeta : beta < cut + p)
    (ha : cut' < a) (horder : a ≤ b) (hb : b < cut' + p)
    (hfirst : ∀ z ∈ D, hamiltonZeroCircleMap phi (j z) ∈
      AddCircle.closedIntervalArc p alpha beta)
    (hsecond : ∀ z ∈ D, hamiltonZeroSecondCircleMap phi (j z) ∈
      AddCircle.closedIntervalArc p a b)
    (theta : C0) (hthird : ∀ z ∈ D, hamiltonZeroThirdCircleMap phi (j z) = theta) :
    let u : C(D, X0) := ⟨fun z => hamiltonZeroAmbientMap phi (j z),
      (hamiltonZeroAmbientMap phi).continuous.comp hj.continuousOn.domRestrict⟩
    ∃ (v w : V2 → ℝ) (q : V2 → X0),
      FinitePiecewiseAffineOn v D ∧ FinitePiecewiseAffineOn w D ∧
      (∀ z ∈ D, v z ∈ Icc alpha beta ∧ w z ∈ Icc a b) ∧
      PolyhedralPLInCharts d q D ∧
      (∀ z ∈ D, Q0 (q z) = ((theta, (w z : C0)), (v z : C0))) ∧
      EqOn q (fun z => hamiltonZeroAmbientMap phi (j z)) Q ∧
      ∃ qD : C(D, X0), (∀ z : D, qD z = q z) ∧
      ∃ H : u.HomotopyRel qD {z : D | (z : V2) ∈ Q},
        ∀ t z, (Q0 (H (t, z))).1.1 = theta ∧
          (Q0 (H (t, z))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (H (t, z))).1.2 ∈ AddCircle.closedIntervalArc p a b := by
  intro u
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKD, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  let B := K.frontierSubcomplex D
  have hB : B.faces.Finite := K.frontierSubcomplex_finite _ hK
  have hBQ : B.space = Q := by
    rw [K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKD,
      frontier_closedBall _ one_ne_zero]
  have hBK : B.space ⊆ K.space := by
    rw [hBQ, hKD]
    exact sphere_subset_closedBall
  have hjK : PolyhedralPLInCharts e j K.space := hKD.symm ▸ hj
  obtain ⟨v0, hv0, hrangev0, hliftv0⟩ := finitePL_arc_coordinate e
    (hamiltonZeroCircleMap phi) K hK j hjK halpha hbeta
    (fun z hz => hfirst z (hKD.subset hz))
    (fun i => hphi.locallyPL_hamiltonZero_circle_coordinate hd cut i)
  obtain ⟨w0, hw0, hrangew0, hliftw0⟩ := finitePL_arc_coordinate e
    (hamiltonZeroSecondCircleMap phi) K hK j hjK ha hb
    (fun z hz => hsecond z (hKD.subset hz))
    (fun i => locallyPL_hamiltonZero_second_circle_coordinate e d hd phi hphi cut' i)
  obtain ⟨v, hv, hkeepv, hrangev⟩ := exists_bounded_scalar_boundary_extension
    K B hK hBK v0 (hv0.restrict B hB hBK) hab (fun z hz => hrangev0 z (hBK hz))
  obtain ⟨w, hw, hkeepw, hrangew⟩ := exists_bounded_scalar_boundary_extension
    K B hK hBK w0 (hw0.restrict B hB hBK) horder (fun z hz => hrangew0 z (hBK hz))
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
  have hq : PolyhedralPLInCharts d q K.space := by
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
  have hqD : PolyhedralPLInCharts d q D := hKD ▸ hq
  let vc : C(D, ℝ) := ⟨fun z => v z, (hKD ▸ hv.continuousOn).domRestrict⟩
  let wc : C(D, ℝ) := ⟨fun z => w z, (hKD ▸ hw.continuousOn).domRestrict⟩
  let v0c : C(D, ℝ) := ⟨fun z => v0 z, (hKD ▸ hv0.continuousOn).domRestrict⟩
  let w0c : C(D, ℝ) := ⟨fun z => w0 z, (hKD ▸ hw0.continuousOn).domRestrict⟩
  have hqbound : EqOn q (fun z => hamiltonZeroAmbientMap phi (j z)) Q := by
    intro z hz
    have hzK := hKD.symm.subset (sphere_subset_closedBall hz)
    apply (Q0).injective
    rw [hqcoord, hkeepv (hBQ.symm.subset hz), hkeepw (hBQ.symm.subset hz),
      hliftv0 z hzK, hliftw0 z hzK]
    exact Prod.ext (Prod.ext (hthird z (hKD.subset hzK)).symm rfl) rfl
  let qD : C(D, X0) := ⟨fun z => q z, hqD.continuousOn.domRestrict⟩
  let mix (f g : C(D, ℝ)) : C(unitInterval × D, ℝ) :=
    ⟨fun z => (1 - (z.1 : ℝ)) * f z.2 + (z.1 : ℝ) * g z.2, by fun_prop⟩
  let G : C(unitInterval × D, X0) := ⟨fun z => (Q0).symm
    ((theta, ((mix w0c wc z : ℝ) : C0)), ((mix v0c vc z : ℝ) : C0)), by fun_prop⟩
  have hGcoord (t : unitInterval) (z : D) : Q0 (G (t, z)) =
      ((theta, ((mix w0c wc (t, z) : ℝ) : C0)), ((mix v0c vc (t, z) : ℝ) : C0)) :=
    (Q0).apply_symm_apply _
  let H : u.HomotopyRel qD {z : D | (z : V2) ∈ Q} := {
    toFun := G
    continuous_toFun := G.continuous
    map_zero_left := by
      intro z
      apply (Q0).injective
      rw [hGcoord]
      simp only [mix, ContinuousMap.coe_mk, Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
      change ((theta, ((w0 z : ℝ) : C0)), ((v0 z : ℝ) : C0)) = _
      rw [hliftv0 z (hKD.symm.subset z.property), hliftw0 z (hKD.symm.subset z.property)]
      exact Prod.ext (Prod.ext (hthird z z.property).symm rfl) rfl
    map_one_left := by
      intro z
      apply (Q0).injective
      rw [hGcoord]
      change ((theta, ((mix w0c wc (1, z) : ℝ) : C0)),
        ((mix v0c vc (1, z) : ℝ) : C0)) = Q0 (q z)
      rw [hqcoord]
      simp only [mix, ContinuousMap.coe_mk, Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
      rfl
    prop' := by
      intro t z hz
      apply (Q0).injective
      change Q0 (G (t, z)) = Q0 (u z)
      rw [hGcoord]
      have hvz : vc z = v0c z := hkeepv (hBQ.symm.subset hz)
      have hwz : wc z = w0c z := hkeepw (hBQ.symm.subset hz)
      have hm (f g : C(D, ℝ)) (heq : g z = f z) : mix f g (t, z) = f z := by
        dsimp [mix]
        rw [heq]
        ring
      rw [hm _ _ hwz, hm _ _ hvz]
      change ((theta, ((w0 z : ℝ) : C0)), ((v0 z : ℝ) : C0)) = _
      rw [hliftv0 z (hKD.symm.subset z.property), hliftw0 z (hKD.symm.subset z.property)]
      exact Prod.ext (Prod.ext (hthird z z.property).symm rfl) rfl }
  refine ⟨v, w, q, hKD ▸ hv, hKD ▸ hw, ?_, hqD, fun z _ => hqcoord z, hqbound,
    qD, fun _ => rfl, H, ?_⟩
  · intro z hz
    exact ⟨hrangev z (hKD.symm.subset hz), hrangew z (hKD.symm.subset hz)⟩
  · intro t z
    rw [show H (t, z) = G (t, z) from rfl, hGcoord]
    refine ⟨rfl, ⟨mix v0c vc (t, z), ?_, rfl⟩, ⟨mix w0c wc (t, z), ?_, rfl⟩⟩
    · exact (convex_Icc alpha beta) (hrangev0 z (hKD.symm.subset z.property))
        (hrangev z (hKD.symm.subset z.property)) (sub_nonneg.mpr t.property.2) t.property.1
        (by ring)
    · exact (convex_Icc a b) (hrangew0 z (hKD.symm.subset z.property))
        (hrangew z (hKD.symm.subset z.property)) (sub_nonneg.mpr t.property.2) t.property.1
        (by ring)

end PoincareConjecture.M76
