import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Push.BaseCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Push.ProductSide
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Push.ArcCutoff



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

theorem exists_original_relative_proper_disk_push
    {X ι E B : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace B] [CompactSpace B] [PreconnectedSpace B]
    {e : ι → OpenPartialHomeomorph X V3} {R A T Z O : Set X}
    (hR : IsCompact R) (he : PLDomain e R)
    {j : V2 → X} (hj : PolyhedralPLInCharts e j Disk) (hji : InjOn j Disk)
    (hjR : MapsTo j Disk R) (hjproper : ∀ x ∈ Disk, j x ∈ frontier R ↔ x ∈ Rim)
    (hO : IsOpen O) (hjO : j '' Disk ⊆ O)
    {d q W : Set E} {a b : E}
    (hd : IsFinitePLBallPair P2 d q) (hW : IsFinitePLBallPair ℝ W {a, b})
    (hWq : W ⊆ q) (hab : a ≠ b)
    {f : E → X} (hf : PolyhedralPLInCharts e f d) (hfi : InjOn f d)
    (hsubset : f '' d ⊆ j '' Disk)
    (hA : IsClosed A) (hT : IsClosed T) (hZ : IsClosed Z)
    (hWA : Disjoint (f '' W) A) (hfZ : Disjoint (f '' d) Z)
    (hfT : ∀ x ∈ d, f x ∈ T ↔ x ∈ W)
    (p : B × J → X) (hp : Continuous p) (hpR : ∀ z, p z ∈ R)
    (hp0 : ∀ b, p (b, ⟨0, by norm_num⟩) ∈ j '' Disk)
    (hpzero : ∀ z, p z ∈ j '' Disk ↔ (z.2 : ℝ) = 0)
    (hcover : A ⊆ (j '' Disk) ∪ range p ∪ Z) :
    ∃ k : E → X, PolyhedralPLInCharts e k d ∧ InjOn k d ∧
      MapsTo k d R ∧ MapsTo k d O ∧ EqOn k f W ∧
      Disjoint (k '' d) A ∧ (∀ x ∈ d, k x ∈ T ↔ x ∈ W) ∧
      ∀ x ∈ d, k x ∈ frontier R ↔ f x ∈ frontier R := by
  obtain ⟨u, hu, hui, humap, hvalue⟩ :=
    exists_original_subdisk_coordinates he.compatible hd hf hfi hj hji hsubset
  let qu : d → Disk := fun x ↦ ⟨u x, humap x.property⟩
  have hqu : Continuous qu := hu.continuousOn.domRestrict.subtype_mk _
  let Q : Set Disk := range qu
  let : CompactSpace d := isCompact_iff_compactSpace.mp hd.isCompact
  have hQ : IsCompact Q := isCompact_range hqu
  have hQZ (z : Disk) (hz : z ∈ Q) : j z ∉ Z := by
    obtain ⟨x, rfl⟩ := hz
    change j (u x) ∉ Z
    rw [hvalue x x.property]
    exact fun hxZ ↦ Set.disjoint_left.mp hfZ ⟨x, x.property, rfl⟩ hxZ
  obtain ⟨P, δ, positive, hPO, hδ, hδhalf, havoid⟩ :=
    exists_original_proper_disk_opposite_product hR he hj hji hjR hjproper hO hjO
      p hp hpR hp0 hpzero hQ hZ hQZ hcover
  let contact := d ∩ f ⁻¹' A
  have hcontact : IsCompact contact := hd.isCompact.of_isClosed_subset
    (hf.continuousOn.preimage_isClosed_of_isClosed hd.isCompact.isClosed hA) inter_subset_left
  have hcontactd : contact ⊆ d \ W := by
    intro x hx
    exact ⟨hx.1, fun hxW ↦ Set.disjoint_left.mp hWA ⟨x, hxW, rfl⟩ hx.2⟩
  obtain ⟨w, K, hw, hK, hKd, hCK, hwbound, hwpos, hwzero⟩ :=
    exists_finitePL_disk_arc_cutoff hd hW hWq hab hcontact hcontactd
      (by norm_num : (0 : ℝ) < 1)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let g : K × I → X := fun z ↦ P.map (u z.1, (z.2 : ℝ))
  have hg : Continuous g := P.polyhedral.continuousOn.comp_continuous
    ((hu.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_fst)
      (fun z ↦ (hKd z.1.property).1)).prodMk
        (continuous_subtype_val.comp continuous_snd))
    (fun z ↦ ⟨humap (hKd z.1.property).1, z.2.property⟩)
  obtain ⟨r, hr, _, hthin⟩ := hg.exists_closed_strip_subset hT.isOpen_compl (by
    intro x
    change P.map (u x, 0) ∉ T
    rw [P.central _ (humap (hKd x.property).1), hvalue _ (hKd x.property).1]
    exact fun h ↦ (hKd x.property).2 ((hfT x (hKd x.property).1).mp h))
  let ε := min δ r
  have hε : 0 < ε := lt_min hδ hr
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεr : ε ≤ r := min_le_right _ _
  let v : E → ℝ := fun x ↦ if positive then -(ε * w x) else ε * w x
  have hv : FinitePiecewiseAffineOn v d := by
    cases positive
    · exact (hw.postcomp (ε • ContinuousAffineMap.id ℝ ℝ)).congr (fun _ _ ↦ rfl)
    · exact (hw.postcomp ((-ε) • ContinuousAffineMap.id ℝ ℝ)).congr
        (fun x _ ↦ by simp [v])
  have hvabs (x : E) (hx : x ∈ d) : |v x| ≤ ε := by
    have hwx := hwbound x hx
    have hmul : 0 ≤ ε * w x := mul_nonneg hε.le hwx.1
    have hle : ε * w x ≤ ε := by nlinarith [hwx.2]
    cases positive <;> simp only [v, Bool.false_eq_true, reduceIte, abs_neg,
      abs_of_nonneg hmul] <;> exact hle
  have hvI (x : E) (hx : x ∈ d) : v x ∈ I := by
    have hh := abs_le.mp (hvabs x hx)
    constructor <;> linarith
  have hvzero (x : E) (hx : x ∈ d \ K) : v x = 0 := by
    simp only [v, hwzero x hx, mul_zero, neg_zero, ite_self]
  obtain ⟨L, hL, hLd, hLf⟩ := hu
  have hgraph : FinitePiecewiseAffineOn (fun x ↦ (u x, v x)) d :=
    (show FinitePiecewiseAffineOn u d from ⟨L, hL, hLd, hLf⟩).prod_mk hv
  let k : E → X := fun x ↦ P.map (u x, v x)
  have hk : PolyhedralPLInCharts e k d := by
    rw [← hLd]
    exact P.polyhedral.comp_finitePiecewiseAffineOn L hL (hLd.symm ▸ hgraph)
      (fun x hx ↦ ⟨humap (hLd.subset hx), hvI x (hLd.subset hx)⟩)
  have hki : InjOn k d := by
    intro x hx y hy hxy
    exact hui hx hy (congrArg Prod.fst (P.injective
      ⟨humap hx, hvI x hx⟩ ⟨humap hy, hvI y hy⟩ hxy))
  have hkeep (x : E) (hx : x ∈ W) : k x = f x := by
    have hxd := hd.1 (hWq hx)
    change P.map (u x, v x) = f x
    rw [hvzero x ⟨hxd, fun hxK ↦ (hKd hxK).2 hx⟩,
      P.central _ (humap hxd), hvalue x hxd]
  refine ⟨k, hk, hki, fun x hx ↦ P.inside ⟨humap hx, hvI x hx⟩,
    fun x hx ↦ hPO ⟨humap hx, hvI x hx⟩, hkeep, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hy
    by_cases hweight : w x = 0
    · have hvx : v x = 0 := by simp only [v, hweight, mul_zero, neg_zero, ite_self]
      have hfx : f x ∈ A := by
        simpa only [k, hvx, P.central _ (humap hx), hvalue x hx] using hy
      exact (ne_of_gt (hwpos x ⟨hx, hfx⟩)) hweight
    · apply havoid ⟨u x, humap hx⟩ ⟨⟨x, hx⟩, rfl⟩ ⟨v x, hvI x hx⟩ _ hy
      have hwp : 0 < w x := lt_of_le_of_ne (hwbound x hx).1 (Ne.symm hweight)
      have hm : 0 < ε * w x := mul_pos hε hwp
      have hmle : ε * w x ≤ δ := by nlinarith [(hwbound x hx).2]
      cases positive <;> simp only [v, Bool.false_eq_true, reduceIte]
      · exact ⟨hm, hmle⟩
      · exact ⟨by linarith, by linarith⟩
  · intro x hx
    constructor
    · intro hkt
      by_cases hxK : x ∈ K
      · exact (hthin ⟨x, hxK⟩ ⟨v x, hvI x hx⟩ ((hvabs x hx).trans hεr) hkt).elim
      · have hfx : f x ∈ T := by
          simpa only [k, hvzero x ⟨hx, hxK⟩, P.central _ (humap hx), hvalue x hx] using hkt
        exact (hfT x hx).mp hfx
    · intro hxW
      rw [hkeep x hxW]
      exact (hfT x hx).mpr hxW
  · intro x hx
    exact (P.proper _ ⟨humap hx, hvI x hx⟩).trans
      ((hjproper _ (humap hx)).symm.trans (by rw [hvalue x hx]))

end PoincareConjecture.M76.Dehn.Annuli
