import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Geometry.ComponentBicollar
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Geometry.InteriorBall
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.SourcePhaseSets
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalBallBicollarEnlargement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.OriginalBallBoundarySphere
import Mathlib.Topology.Order.IntermediateValue









set_option autoImplicit false
open Set Geometry

namespace AddCircle




theorem exists_closed_arc_of_compact_connected
    {X : Type*} [TopologicalSpace X] (period : ℝ) [Fact (0 < period)]
    {S : Set X} (hS : IsCompact S) (hconn : IsConnected S)
    (q : X → AddCircle period) (hq : ContinuousOn q S)
    (htarget : MapsTo q S (openPartialHomeomorphCoe period (0 : ℝ)).target)
    (a b : ℝ) (havoid : ∀ x ∈ S, q x ≠ (a : AddCircle period) ∧
      q x ≠ (b : AddCircle period)) :
    ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ upper ∧ upper < period ∧
      a ∉ Icc lower upper ∧ b ∉ Icc lower upper ∧
      q '' S = ((↑) : ℝ → AddCircle period) '' Icc lower upper := by
  let chart := openPartialHomeomorphCoe period (0 : ℝ)
  let f : X → ℝ := chart.symm ∘ q
  have hf : ContinuousOn f S := chart.symm.continuousOn.comp hq htarget
  have hfrange (x : X) (hx : x ∈ S) : 0 < f x ∧ f x < period := by
    have hh := chart.map_target (htarget hx)
    change 0 < f x ∧ f x < 0 + period at hh
    simpa only [zero_add] using hh
  have hcoe (x : X) (hx : x ∈ S) : (f x : AddCircle period) = q x :=
    chart.right_inv (htarget hx)
  obtain ⟨xmin, hxmin, hmin⟩ := hS.exists_isMinOn hconn.nonempty hf
  obtain ⟨xmax, hxmax, hmax⟩ := hS.exists_isMaxOn hconn.nonempty hf
  have himage : f '' S = Icc (f xmin) (f xmax) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨hmin hx, hmax hx⟩
    · exact (hconn.isPreconnected.image f hf).ordConnected.out
        (mem_image_of_mem f hxmin) (mem_image_of_mem f hxmax)
  have havoids (t : ℝ) (ht : t = a ∨ t = b) : t ∉ Icc (f xmin) (f xmax) := by
    intro hmem
    obtain ⟨x, hx, hxt⟩ := himage.symm.subset hmem
    have heq : q x = (t : AddCircle period) := (hcoe x hx).symm.trans (congrArg _ hxt)
    rcases ht with rfl | rfl
    · exact (havoid x hx).1 heq
    · exact (havoid x hx).2 heq
  refine ⟨f xmin, f xmax, (hfrange xmin hxmin).1, hmin hxmax,
    (hfrange xmax hxmax).2, havoids a (Or.inl rfl), havoids b (Or.inr rfl), ?_⟩
  rw [← himage, image_image]
  apply image_congr
  intro x hx
  exact (hcoe x hx).symm

end AddCircle

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩





theorem exists_closed_source_component_boundary_arc_ball
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3) (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (hI : IsPLIrreducible e R)
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {u v a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    {theta theta' : C}
    (hpair : (theta = (a : C) ∧ theta' = (b : C)) ∨
      (theta = (b : C) ∧ theta' = (a : C)))
    (heN : PLDomain e (sourceSlab phi u v))
    (hfront : frontier (sourceSlab phi u v) = (sourceSlab phi u v ∩ frontier R) ∪
      (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hAB : Disjoint (sourceSurface phi theta) (sourceSurface phi theta'))
    (hcorner : ∀ x ∈ sourceSurface phi theta ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
        x ∈ G.source ∧ psi (G x) = 0 ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ∩ frontier R ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ sourceSurface phi theta ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0)
    (hinj : ∀ x : sourceSurface phi theta, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X)) x))
    {S U : Set X} (hSne : S.Nonempty) (hS : S ⊆ sourceSurface phi theta)
    (hcomponent : ∀ x ∈ S, connectedComponentIn (sourceSurface phi theta) x = S)
    (hrim : Disjoint S (frontier R)) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ D D' S' : Set X, Nonempty (ChartwisePLBall e D S) ∧
      Nonempty (ChartwisePLBall e D' S') ∧ IsCompact D ∧ IsCompact D' ∧
      D' ⊆ interior R ∧ D ⊆ interior D' ∧ S ⊆ interior D' ∧ D' ⊆ D ∪ U ∧ S' ⊆ U ∧
      ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ upper ∧ upper < p ∧
        a ∉ Icc lower upper ∧ b ∉ Icc lower upper ∧
        ambientSourcePhase phi '' S' = ((↑) : ℝ → C) '' Icc lower upper := by
  let : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space
  have hSint : S ⊆ interior R := by
    intro x hx
    by_contra hn
    apply disjoint_left.mp hrim hx
    rw [hI.1.closed.frontier_eq]
    exact ⟨sourceSurface_subset phi theta (hS hx), hn⟩
  obtain ⟨sph⟩ := exists_closed_source_component_sphere e d phi hphi F0 heN hfront
    hAB hcorner hinj hSne hS hcomponent hrim
  obtain ⟨D, hDcompact, hDint, ⟨ball⟩⟩ :=
    hI.exists_compact_ball_subset_interior hSint ⟨sph⟩
  let chart := AddCircle.openPartialHomeomorphCoe p (0 : ℝ)
  let W : Set X := U ∩ (interior R ∩ ambientSourcePhase phi ⁻¹' chart.target)
  have hW : IsOpen W := hU.inter
    (((continuousOn_ambientSourcePhase phi).mono interior_subset).isOpen_inter_preimage
      isOpen_interior chart.open_target)
  have haT : (a : C) ∈ chart.target := chart.map_source (by
    change 0 < a ∧ a < 0 + p
    exact ⟨ha, by linarith⟩)
  have hbT : (b : C) ∈ chart.target := chart.map_source (by
    change 0 < b ∧ b < 0 + p
    exact ⟨ha.trans hab, by linarith⟩)
  have hthetaT : theta ∈ chart.target := by
    rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact haT
    · exact hbT
  have hSW : S ⊆ W := by
    intro x hx
    refine ⟨hSU hx, hSint hx, ?_⟩
    have hphase := hS hx
    rw [sourceSurface_eq_inter_phase] at hphase
    change ambientSourcePhase phi x ∈ chart.target
    rw [show ambientSourcePhase phi x = theta from hphase.2]
    exact hthetaT
  obtain ⟨t, K, HB, c, r, hK, hr, hrhalf, hc, hi, hbase, hmaps, hf, hopen, _⟩ :=
    exists_closed_source_component_bicollar e d phi hphi F0 heN hfront hAB hcorner
      hinj hSne hS hcomponent hrim hW hSW
  have hsub : K.space ×ˢ Icc (-r) r ⊆ K.space ×ˢ Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_interval_product hK (by linarith : -r < r)
  have hcsmall : PolyhedralPLInCharts e c (K.space ×ˢ Icc (-r) r) :=
    hJs ▸ hc.restrict_finite J hJ (hJs.subset.trans hsub)
  have hismall : Topology.IsEmbedding
      (fun z : (K.space ×ˢ Icc (-r) r : Set ((t → ℝ × V3) × ℝ)) => c z) :=
    hi.comp (Topology.IsEmbedding.subtypeVal.codRestrict _ (fun z => hsub z.property))
  obtain ⟨level, hlevel, hlevel0, D', ⟨ballNew⟩, hDD', hD'sub⟩ :=
    ball.exists_bicollar_enlargement sph hI.1.cover hI.1.compatible K hK HB c hr
      hcsmall hismall hbase (hopen r hr le_rfl)
  let S' : Set X := c '' (K.space ×ˢ {level})
  have hlevelI : level ∈ Icc (-r) r := by
    rcases hlevel with rfl | rfl <;> constructor <;> linarith
  have hS'small : S' ⊆ c '' (K.space ×ˢ Icc (-r) r) :=
    image_mono (prod_mono Subset.rfl (singleton_subset_iff.mpr hlevelI))
  have hsmallW : c '' (K.space ×ˢ Icc (-r) r) ⊆ W := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hmaps hz).1
  have hsmallint : c '' (K.space ×ˢ Icc (-r) r) ⊆ interior R := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hmaps hz).2
  have hS'W : S' ⊆ W := hS'small.trans hsmallW
  have hS'notfront : Disjoint S' (frontier (sourceSlab phi u v)) := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hxfront
    have hzt : z.2 = level := hz.2
    exact hlevel0 (hzt.symm.trans ((hf z ⟨hz.1, hzt.symm ▸ hlevelI⟩).mp hxfront))
  have hphases : sourceSurface phi (a : C) ∪ sourceSurface phi (b : C) =
      sourceSurface phi theta ∪ sourceSurface phi theta' := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact union_comm _ _
  have hmarked : sourceSurface phi (a : C) ∪ sourceSurface phi (b : C) ⊆
      frontier (sourceSlab phi u v) := by
    rw [hphases, hfront]
    exact subset_union_right
  have havoid (x : X) (hx : x ∈ S') :
      ambientSourcePhase phi x ≠ (a : C) ∧ ambientSourcePhase phi x ≠ (b : C) := by
    have hxR : x ∈ R := interior_subset (hsmallint (hS'small hx))
    constructor
    · intro heq
      apply disjoint_left.mp hS'notfront hx
      apply hmarked
      apply Or.inl
      rw [sourceSurface_eq_inter_phase]
      exact ⟨hxR, heq⟩
    · intro heq
      apply disjoint_left.mp hS'notfront hx
      apply hmarked
      apply Or.inr
      rw [sourceSurface_eq_inter_phase]
      exact ⟨hxR, heq⟩
  obtain ⟨sphereNew⟩ := ballNew.nonempty_boundarySphere
  have hS'compact : IsCompact S' := ballNew.isCompact.of_isClosed_subset
    (by change IsClosed (c '' (K.space ×ˢ {level}))
        rw [← ballNew.frontier_eq]
        exact isClosed_frontier) ballNew.boundary_subset
  have harc := AddCircle.exists_closed_arc_of_compact_connected p hS'compact
    sphereNew.isConnected (ambientSourcePhase phi)
    ((continuousOn_ambientSourcePhase phi).mono
      (hS'small.trans hsmallint |>.trans interior_subset))
    (fun x hx => (hS'W hx).2.2) a b havoid
  exact ⟨D, D', S', ⟨ball⟩, ⟨ballNew⟩, hDcompact, ballNew.isCompact,
    hD'sub.trans (union_subset hDint hsmallint), hDD', ball.boundary_subset.trans hDD',
    hD'sub.trans (union_subset_union_right D (hsmallW.trans inter_subset_left)),
    hS'W.trans inter_subset_left, harc⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
