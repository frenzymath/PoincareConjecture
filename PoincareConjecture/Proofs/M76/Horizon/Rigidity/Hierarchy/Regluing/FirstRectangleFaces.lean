import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.RectangleFaces
import PoincareConjecture.Proofs.M76.Wall.OriginalFrontierSurfaceModel
import Mathlib.Topology.Separation.Connected










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates



def HamiltonZeroFirstRectangleFaces {ι : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (R : Set X0) (phi : C(H0, H0))
    (alpha beta a b u v : ℝ) : Prop :=
  ∃ (n : ℕ)
    (face : Fin n → C((Icc a b ×ˢ Icc u v : Set (ℝ × ℝ)), frontier R))
    (param : Fin n → (ℝ × ℝ) → X0) (delta : Fin n → ℝ),
    (∀ i, Topology.IsEmbedding (face i)) ∧
    (∀ i, PolyhedralPLInCharts e (param i) (Icc a b ×ˢ Icc u v)) ∧
    (∀ i (t : (Icc a b ×ˢ Icc u v : Set (ℝ × ℝ))), param i t = (face i t : X0)) ∧
    (∀ i, delta i ∈ ({alpha, beta} : Set ℝ)) ∧
    Pairwise (fun i k => Disjoint (range (fun t => (face i t : X0)))
      (range (fun t => (face k t : X0)))) ∧
    (⋃ i, range (fun t => (face i t : X0))) =
      (frontier R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) ∩
        hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v ∧
    ∀ i t, Q0 (hamiltonZeroAmbientMap phi (face i t)) =
      ((((t : ℝ × ℝ).2 : C0), ((t : ℝ × ℝ).1 : C0)), (delta i : C0))

private theorem polyhedralPL_hamiltonZero_first_rectangle
    {κ : Type*} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite) (delta : ℝ) :
    PolyhedralPLInCharts d (fun z : ℝ × ℝ =>
      (Q0).symm (((z.2 : C0), (z.1 : C0)), (delta : C0))) K.space := by
  let linear : (ℝ × ℝ) →L[ℝ] V3 := ContinuousLinearMap.pi
    ![ContinuousLinearMap.snd ℝ ℝ ℝ, ContinuousLinearMap.fst ℝ ℝ ℝ, 0]
  let lift : (ℝ × ℝ) →ᴬ[ℝ] ((Fin 0 ⊕ Fin 3) → ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 0) (Fin 3)
      (fun _ => ℝ)).symm.toContinuousAffineEquiv.toContinuousAffineMap.comp
      ((ContinuousAffineMap.const ℝ (ℝ × ℝ) (0 : Fin 0 → ℝ)).prod
        (linear.toContinuousAffineMap +
          ContinuousAffineMap.const ℝ (ℝ × ℝ) ![0, 0, delta]))
  have hlift : FinitePiecewiseAffineOn lift K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine lift⟩
  apply (hd.polyhedralPL_projection hlift).congr
  intro z _
  apply (Q0).injective
  rw [(Q0).apply_symm_apply]
  change (((((z.2 + 0 : ℝ) : C0), ((z.1 + 0 : ℝ) : C0)), ((0 + delta : ℝ) : C0))) = _
  simp only [add_zero, zero_add]

theorem exists_hamiltonZero_original_first_rectangle_faces
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {R : Set X0} (he : PLDomain e R) (hR : IsCompact R) (hRne : R.Nonempty)
    (g : C(frontier R, C0 × C0)) (hg : IsCoveringMap g)
    (hgval : ∀ x : frontier R, g x = (Q0 (hamiltonZeroAmbientMap phi x)).1)
    {alpha beta : ℝ}
    (hfront : frontier R ⊆ hamiltonZeroCircleMap phi ⁻¹' {(alpha : C0), (beta : C0)})
    {a b u v : ℝ} (hab : a < b) (habwidth : b < a + p)
    (huv : u < v) (huvwidth : v < u + p) :
    HamiltonZeroFirstRectangleFaces e R phi alpha beta a b u v := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace (frontier R) := isCompact_iff_compactSpace.mp
    (hR.of_isClosed_subset isClosed_frontier he.closed.frontier_subset)
  let Rect := (Icc a b ×ˢ Icc u v : Set (ℝ × ℝ))
  have hconvex : Convex ℝ Rect := (convex_Icc a b).prod (convex_Icc u v)
  let t0 : Rect := ⟨(a, u), ⟨le_rfl, hab.le⟩, le_rfl, huv.le⟩
  let : ContractibleSpace Rect := hconvex.contractibleSpace ⟨t0, t0.property⟩
  let : LocallyPathConnectedSpace Rect := hconvex.locallyPathConnectedSpace
  let : CompactSpace Rect := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  let base : C(Rect, C0 × C0) :=
    ⟨fun t => (((t : ℝ × ℝ).2 : C0), ((t : ℝ × ℝ).1 : C0)), by fun_prop⟩
  have hbase : Function.Injective base := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
        ⟨x.property.1.1, x.property.1.2.trans_lt habwidth⟩
        ⟨y.property.1.1, y.property.1.2.trans_lt habwidth⟩).mp (congrArg Prod.snd hxy)
    · exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
        ⟨x.property.2.1, x.property.2.2.trans_lt huvwidth⟩
        ⟨y.property.2.1, y.property.2.2.trans_lt huvwidth⟩).mp (congrArg Prod.fst hxy)
  obtain ⟨n, face, hi, hdis, hwhole, hcoord⟩ :=
    hg.exists_finite_lifted_compact_family base hbase t0
  have hnormal (i : Fin n) (t : Rect) :
      hamiltonZeroCircleMap phi (face i t) = hamiltonZeroCircleMap phi (face i t0) := by
    let f : C(Rect, C0) := ⟨fun t => hamiltonZeroCircleMap phi (face i t), by fun_prop⟩
    have hfinite : (range f).Finite := ((finite_singleton (beta : C0)).insert (alpha : C0)).subset (by
      rintro _ ⟨s, rfl⟩
      exact hfront (face i s).property)
    by_contra hne
    exact hfinite.not_infinite ((isPreconnected_range f.continuous).infinite_of_nontrivial
      ⟨f t, mem_range_self t, f t0, mem_range_self t0, hne⟩)
  have hlabels (i : Fin n) : ∃ delta ∈ ({alpha, beta} : Set ℝ),
      (delta : C0) = hamiltonZeroCircleMap phi (face i t0) := by
    rcases hfront (face i t0).property with h | h
    · exact ⟨alpha, Or.inl rfl, h.symm⟩
    · exact ⟨beta, Or.inr rfl, h.symm⟩
  choose delta hdelta hdelta0 using hlabels
  have htarget (i : Fin n) (t : Rect) : Q0 (hamiltonZeroAmbientMap phi (face i t)) =
      ((((t : ℝ × ℝ).2 : C0), ((t : ℝ × ℝ).1 : C0)), (delta i : C0)) := by
    apply Prod.ext
    · exact (hgval (face i t)).symm.trans (hcoord i t)
    · rw [hamiltonZeroAmbientMap_circle, hnormal, hdelta0]
  obtain ⟨s, F, K, A, H, inverse, HB, _, _, hK, hAK, hA, _, _, _, _, _, _,
    hinversePL, hHB, _, _, _⟩ := he.exists_original_frontier_surface_model hR hRne
  let inv : (s → ℝ × V3) → X0 := fun z => inverse z
  have hAsub := SimplicialComplex.space_subset_of_le hAK
  have hinvPL : PolyhedralPLInCharts e inv A.space := hinversePL.restrict_finite A hA hAsub
  let Y : (s → ℝ × V3) → X0 := fun z => hamiltonZeroAmbientMap phi (inv z)
  have hY : PolyhedralPLInCharts d Y A.space :=
    hphi.polyhedralPL_hamiltonZeroAmbientMap_comp A hA hinvPL
  have hYinj : IsLocallyInjective (fun x : A.space => Y x) := by
    intro x
    obtain ⟨U, hU, hxU, hgU⟩ := hg.isLocalHomeomorph.isLocallyInjective (HB x)
    refine ⟨HB ⁻¹' U, hU.preimage HB.continuous, hxU, ?_⟩
    intro y hy z hz heq
    apply HB.injective
    apply hgU hy hz
    rw [hgval, hgval, hHB, hHB]
    exact congrArg (fun z => (Q0 z).1) heq
  let lift (i : Fin n) (z : ℝ × ℝ) : (s → ℝ × V3) :=
    if hz : z ∈ Rect then HB.symm (face i ⟨z, hz⟩) else 0
  have hlift (i : Fin n) (t : Rect) : lift i t = (HB.symm (face i t) : s → ℝ × V3) := by
    simp only [lift, dif_pos t.property]
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLR, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc hab).prod (isFinitePLBallPair_Icc huv)
  have hliftA (i : Fin n) : MapsTo (lift i) L.space A.space := by
    intro z hz
    rw [hlift i ⟨z, hLR.subset hz⟩]
    exact (HB.symm (face i ⟨z, hLR.subset hz⟩)).property
  have hinvface (i : Fin n) (t : Rect) : inv (lift i t) = (face i t : X0) := by
    rw [hlift]
    exact (hHB _).symm.trans (congrArg Subtype.val (HB.apply_symm_apply _))
  have hliftPL (i : Fin n) : FinitePiecewiseAffineOn (lift i) L.space := by
    have hcont : ContinuousOn (lift i) Rect := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (continuous_subtype_val.comp (HB.symm.continuous.comp (face i).continuous)).congr
        (fun t => (hlift i t).symm)
    have hcomp : PolyhedralPLInCharts d (Y ∘ lift i) L.space := by
      apply (polyhedralPL_hamiltonZero_first_rectangle hd L hL (delta i)).congr
      intro z hz
      change _ = hamiltonZeroAmbientMap phi (inv (lift i z))
      rw [hinvface i ⟨z, hLR.subset hz⟩]
      exact (Q0).injective (by rw [(Q0).apply_symm_apply, htarget])
    exact hY.finitePiecewiseAffineOn_lift_of_locallyInjective hphi.target_domain.compatible
      A hA hYinj L hL (show ContinuousOn (lift i) L.space from hLR ▸ hcont)
      (hliftA i) hcomp
  let param : Fin n → (ℝ × ℝ) → X0 := fun i => inv ∘ lift i
  have hparamPL (i : Fin n) : PolyhedralPLInCharts e (param i) Rect := by
    simpa only [Rect, hLR] using hinvPL.comp_finitePiecewiseAffineOn L hL (hliftPL i) (hliftA i)
  refine ⟨n, face, param, delta, hi, hparamPL, hinvface, hdelta, ?_, ?_, htarget⟩
  · intro i k hik
    apply disjoint_left.mpr
    rintro x ⟨s, rfl⟩ ⟨t, hts⟩
    exact disjoint_left.mp (hdis hik) (mem_range_self s) ⟨t, Subtype.ext hts⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hx
      refine ⟨⟨(face i t).property, ?_⟩, ?_⟩
      · change hamiltonZeroSecondCircleMap phi (face i t) ∈ AddCircle.closedIntervalArc p a b
        rw [hamiltonZeroSecondCircleMap_ambient, htarget]
        exact ⟨(t : ℝ × ℝ).1, t.property.1, rfl⟩
      · change hamiltonZeroThirdCircleMap phi (face i t) ∈ AddCircle.closedIntervalArc p u v
        rw [hamiltonZeroThirdCircleMap_ambient, htarget]
        exact ⟨(t : ℝ × ℝ).2, t.property.2, rfl⟩
    · rintro ⟨⟨hx, s, hs, hsx⟩, t, ht, htx⟩
      have hmem : (⟨x, hx⟩ : frontier R) ∈ ⋃ i, range (face i) := by
        rw [hwhole]
        refine ⟨⟨(s, t), hs, ht⟩, ?_⟩
        rw [hgval]
        apply Prod.ext
        · exact htx.trans (hamiltonZeroThirdCircleMap_ambient phi x)
        · exact hsx.trans (hamiltonZeroSecondCircleMap_ambient phi x)
      obtain ⟨i, z, hz⟩ := mem_iUnion.mp hmem
      exact mem_iUnion.mpr ⟨i, z, congrArg Subtype.val hz⟩




theorem exists_hamiltonZero_installed_frontier_tangential_covering
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    {R : Set X0} {r : ℝ} (hr : 0 ≤ r) (c : E × ℝ → X0)
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (phi psi : C(H0, H0))
    (F : (hamiltonZeroAmbientMap phi).HomotopyRel
      (hamiltonZeroAmbientMap psi) (interior R)ᶜ)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g)
    (hproduct : ∀ x : K, (Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1 = g x) :
    ∃ G : C(frontier R, C0 × C0), IsCoveringMap G ∧
      ∀ x : frontier R, G x = (Q0 (hamiltonZeroAmbientMap psi x)).1 := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have h0 : (0 : ℝ) ∈ Icc (-r) r := ⟨neg_nonpos.mpr hr, hr⟩
  have hmem (x : K) : c (x, 0) ∈ frontier R :=
    hzero.subset ⟨(x, 0), ⟨x.property, rfl⟩, rfl⟩
  have hcont : Continuous (fun x : K => c ((x : E), 0)) :=
    hc.comp_continuous (continuous_subtype_val.prodMk continuous_const)
      (fun x => ⟨x.property, h0⟩)
  let zero : C(K, frontier R) := ⟨fun x => ⟨c (x, 0), hmem x⟩, hcont.subtype_mk _⟩
  have hbij : Function.Bijective zero := by
    constructor
    · intro x y hxy
      have h := hi.injective (a₁ := ⟨(x, 0), x.property, h0⟩)
        (a₂ := ⟨(y, 0), y.property, h0⟩) (congrArg Subtype.val hxy)
      exact Subtype.ext (congrArg
        (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => (z : E × ℝ).1) h)
    · intro x
      obtain ⟨⟨z, t⟩, ⟨hz, ht⟩, hzx⟩ := hzero.symm.subset x.property
      have ht0 : t = 0 := ht
      subst t
      exact ⟨⟨z, hz⟩, Subtype.ext hzx⟩
  let H : K ≃ₜ frontier R :=
    (Equiv.ofBijective zero hbij).toHomeomorphOfContinuousClosed
      zero.continuous zero.continuous.isClosedMap
  let G : C(frontier R, C0 × C0) := g.comp ⟨H.symm, H.symm.continuous⟩
  refine ⟨G, hg.comp_homeomorph H.symm, ?_⟩
  intro x
  have hval : c (H.symm x, 0) = x := congrArg Subtype.val (H.apply_symm_apply x)
  have hfixed := F.fst_eq_snd (show (x : X0) ∈ (interior R)ᶜ from x.property.2)
  change g (H.symm x) = _
  rw [← hproduct, hval, hfixed]




theorem exists_hamiltonZero_installed_first_rectangle_faces
    {E ι κ : Type*} [TopologicalSpace E]
    {e : ι → OpenPartialHomeomorph X0 V3} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi psi : C(H0, H0))
    (hpsi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi))
    {R : Set X0} (he : PLDomain e R)
    (F : (hamiltonZeroAmbientMap phi).HomotopyRel
      (hamiltonZeroAmbientMap psi) (interior R)ᶜ)
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X0)
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g)
    (hproduct : ∀ x : K, ∀ t ∈ Icc (-r) r,
      (Q0 (hamiltonZeroAmbientMap phi (c (x, t)))).1 = g x)
    {alpha beta : ℝ}
    (hfront : frontier R ⊆ hamiltonZeroCircleMap phi ⁻¹' {(alpha : C0), (beta : C0)})
    {a b u v : ℝ} (hab : a < b) (habwidth : b < a + p)
    (huv : u < v) (huvwidth : v < u + p) :
    HamiltonZeroFirstRectangleFaces e R psi alpha beta a b u v := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace X0 := (Q0).symm.compactSpace
  obtain ⟨G, hG, hGval⟩ := exists_hamiltonZero_installed_frontier_tangential_covering
    hK hr.le c hc hi hzero phi psi F g hg
      (fun x => hproduct x 0 ⟨by linarith, hr.le⟩)
  obtain ⟨x, hx⟩ := hne
  have hxF : c (x, 0) ∈ frontier R := hzero.subset ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩
  have hRne : R.Nonempty := ⟨c (x, 0), he.closed.frontier_subset hxF⟩
  have hfront' : frontier R ⊆ hamiltonZeroCircleMap psi ⁻¹' {(alpha : C0), (beta : C0)} := by
    intro y hy
    have hfixed := F.fst_eq_snd (show y ∈ (interior R)ᶜ from hy.2)
    have hnormal := congrArg (fun z => (Q0 z).2) hfixed
    rw [hamiltonZeroAmbientMap_circle, hamiltonZeroAmbientMap_circle] at hnormal
    change hamiltonZeroCircleMap psi y ∈ ({(alpha : C0), (beta : C0)} : Set C0)
    rw [← hnormal]
    exact hfront hy
  exact exists_hamiltonZero_original_first_rectangle_faces hd hpsi he he.closed.isCompact hRne
    G hG hGval hfront' hab habwidth huv huvwidth

end PoincareConjecture.M76
