import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalRawCircleCaps
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalCapAnnulusDisk
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusSides

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_retained_side_of_original_annulus
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {S q : Set X} (D : Fin 2 → Set X)
    (hD : ∀ b, IsClosed (D b)) (hwhole : D 0 ∪ D 1 = S)
    (hinter : D 0 ∩ D 1 = q)
    {a : P2 → X} (ha : ContinuousOn a Ann) (haS : a '' Ann ⊆ S)
    (hnew : ∀ x ∈ Ann, a x ∈ q ↔ depth 8 x = 1) (hqA : q ⊆ a '' Ann) :
    ∃ b : Fin 2, a '' Ann ⊆ D b ∧
      (a '' Ann) ∩ D b.rev = q ∧
      (a '' Ann) \ q ⊆ D b \ q := by
  have himage : a '' (Ann \ {x | depth 8 x = 1}) = (a '' Ann) \ q := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx.1,rfl⟩,fun h => hx.2 ((hnew x hx.1).mp h)⟩
    · rintro ⟨⟨x,hx,rfl⟩,hn⟩
      exact ⟨x,⟨hx,fun h => hn ((hnew x hx).mpr h)⟩,rfl⟩
  have hconn : IsPreconnected ((a '' Ann) \ q) := by
    rw [←himage]
    have h := _root_.Dehn.isPreconnected_squareAnnulus_sdiff_depth
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (4 : ℝ) * 1 < 8) true
    have h' : IsPreconnected (Ann \ {x | depth 8 x = 1}) := by simpa using h
    exact h'.image a (ha.mono sdiff_subset)
  have hcover : (a '' Ann) \ q ⊆ D 0 ∪ D 1 :=
    sdiff_subset.trans (haS.trans hwhole.symm.subset)
  have havoid : ((a '' Ann) \ q) ∩ (D 0 ∩ D 1) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx,hx0,hx1⟩
    exact hx.2 (hinter.subset ⟨hx0,hx1⟩)
  have hside := isPreconnected_iff_subset_of_disjoint_closed.mp hconn
    (D 0) (D 1) (hD 0) (hD 1) hcover havoid
  have hex : ∃ b : Fin 2, (a '' Ann) \ q ⊆ D b := by
    rcases hside with h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
  obtain ⟨b,hb⟩ := hex
  have hint : D b ∩ D b.rev = q := by
    fin_cases b
    · simpa using hinter
    · simpa [inter_comm] using hinter
  have hqD : q ⊆ D b := hint.symm.subset.trans inter_subset_left
  have hA : a '' Ann ⊆ D b := by
    intro x hx
    by_cases hq : x ∈ q
    · exact hqD hq
    · exact hb ⟨hx,hq⟩
  refine ⟨b,hA,?_,fun x hx => ⟨hb hx,hx.2⟩⟩
  apply Subset.antisymm
  · exact fun x hx => hint.subset ⟨hA hx.1,hx.2⟩
  · exact fun x hx => ⟨hqA hx,(hint.symm.subset hx).2⟩

theorem ChartwisePLSphere.exists_original_raw_cap_with_annular_disk
    {X E F ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    {r : Set E} (hrT : r ⊆ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)))
    (d : Fin 2 → Set V3) {u : Set V3}
    (hd : ∀ b, IsFinitePLBallPair P2 (d b) u)
    (hwhole : d 0 ∪ d 1 = sphere (0 : V3) 1) (hinter : d 0 ∩ d 1 = u)
    {c q : Set F} {p : F → X} (hc : IsFinitePLBallPair P2 c q)
    (hp : PolyhedralPLInCharts e p c) (hpi : InjOn p c)
    (hcapS : (p '' c) ∩ S = p '' q) (hrim : s.map '' u = p '' q)
    {a : P2 → X} (ha : PolyhedralPLInCharts e a Ann) (hai : InjOn a Ann)
    (haS : a '' Ann ⊆ S)
    (hcap : p '' c ⊆ interior (g '' convexHull ℝ (t : Set E)))
    (haT : a '' Ann ⊆ g '' convexHull ℝ (t : Set E))
    (hain : (a '' Ann) \ (g '' r) ⊆ interior (g '' convexHull ℝ (t : Set E)))
    (hcontact : (p '' c) ∩ (a '' Ann) = p '' q)
    (hinner : ∀ x ∈ Ann, a x ∈ p '' q ↔ depth 8 x = 1)
    (hrA : g '' r ⊆ a '' Ann) (hqA : p '' q ⊆ a '' Ann)
    (houter : ∀ x ∈ Ann, a x ∈ g '' r ↔ depth 8 x = -1) :
    let C := (convexHull ℝ (t : Set E)) ∩ g ⁻¹' ((p '' c) ∪ (a '' Ann))
    ∃ (b : Fin 2) (raw : ∀ k, ChartwisePLSphere e ((s.map '' d k) ∪ (p '' c))),
      (∀ k, EqOn (raw k).map s.map (d k)) ∧
      (∀ k, (raw k).map '' d k.rev = p '' c) ∧
      a '' Ann ⊆ s.map '' d b ∧
      (a '' Ann) ∩ (s.map '' d b.rev) = p '' q ∧
      g '' r ⊆ s.map '' d b ∧ Disjoint (g '' r) (s.map '' d b.rev) ∧
      IsFinitePLBallPair P2 C r ∧
      C ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) = r ∧
      g '' C = (p '' c) ∪ (a '' Ann) ∧
      g '' C ⊆ (s.map '' d b) ∪ (p '' c) ∧
      (g '' C) ∩ ((s.map '' d b.rev) ∪ (p '' c)) = p '' c := by
  obtain ⟨raw,hraw,hrawcap,hphysical,hphysicalrim,_,_,_,_⟩ :=
    s.exists_original_raw_circle_caps he d hd hwhole hinter hc hp hpi hcapS hrim
  have hdS (b : Fin 2) : d b ⊆ sphere (0 : V3) 1 := by
    fin_cases b
    · exact subset_union_left.trans hwhole.subset
    · exact subset_union_right.trans hwhole.subset
  have hclosed (b : Fin 2) : IsClosed (s.map '' d b) :=
    ((hd b).isCompact.image_of_continuousOn (s.piecewiseAffine.continuousOn.mono (hdS b))).isClosed
  obtain ⟨b,hA,hother,_⟩ := exists_retained_side_of_original_annulus
    (fun b => s.map '' d b) hclosed hphysical hphysicalrim ha.continuousOn haS hinner hqA
  have hdisrim : Disjoint (g '' r) (p '' q) := by
    apply disjoint_left.mpr
    intro x hxold hxnew
    obtain ⟨y,hy,hxy⟩ := hrA hxold
    have h1 := (hinner y hy).mp (hxy.symm ▸ hxnew)
    have hm1 := (houter y hy).mp (hxy.symm ▸ hxold)
    linarith
  obtain ⟨hball,hproper,himage⟩ := original_cap_annulus_carrier_is_proper_disk
    he K hK hg hgi ht ht4 hrT hc hp hpi ha hai hcap haT hain hcontact hinner hrA houter
  refine ⟨b,raw,hraw,hrawcap,hA,hother,hrA.trans hA,?_,hball,hproper,himage,?_,?_⟩
  · apply disjoint_left.mpr
    intro x hxold hxother
    exact disjoint_left.mp hdisrim hxold (hother.subset ⟨hrA hxold,hxother⟩)
  · rw [himage]
    intro x hx
    exact hx.elim Or.inr (fun h => Or.inl (hA h))
  · rw [himage]
    apply Subset.antisymm
    · rintro x ⟨hxc | hxa,hxo | hxc'⟩
      · exact hxc
      · exact hxc
      · exact image_mono hc.1 (hother.subset ⟨hxa,hxo⟩)
      · exact hxc'
    · intro x hx
      exact ⟨Or.inl hx,Or.inr hx⟩

end PoincareConjecture.M76
