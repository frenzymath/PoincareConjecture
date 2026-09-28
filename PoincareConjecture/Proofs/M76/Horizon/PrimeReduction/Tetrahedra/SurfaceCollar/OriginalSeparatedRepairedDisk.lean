import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalCarrierComponentTransport










set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.OriginalDiskProduct
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "Source" => SProd.sprod Disk (Icc (-1 : ℝ) 1)

theorem exists_original_separated_repaired_disk_transport
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    {T : Set E} (hTK : T ⊆ K.space)
    (hP : MapsTo P.map Source (interior (g '' T))) (hS : S ⊆ g '' K.space)
    (k q : Bool → Set V3)
    (hk : ∀ b, IsFinitePLBallPair (ℝ × ℝ) (k b) (q b) ∧ k b ⊆ Sphere ∧
      s.map '' q b = P.capRimSet b ∧ (s.map '' k b) ∩ P.closedStrip = s.map '' q b) :
    ∃ f : V2 × ℝ → E, FinitePiecewiseAffineOn f Source ∧ InjOn f Source ∧
      MapsTo f Source K.space ∧ (∀ z ∈ Source, g (f z) = P.map z) ∧
      (∀ A : Set (V2 × ℝ), A ⊆ Source → f '' A = K.space ∩ g ⁻¹' (P.map '' A)) ∧
      ∀ b : Bool,
        let D := K.space ∩ g ⁻¹' (s.map '' k b)
        let I := if b then Icc (0 : ℝ) (1/2) else Icc (-(1/2 : ℝ)) 0
        let t := if b then (1/2 : ℝ) else -(1/2)
        let A := D ∪ f '' ((Disk ×ˢ {(0 : ℝ)}) ∪ (Rim ×ˢ I))
        let B := D ∪ f '' (Disk ×ˢ {t})
        ∃ h : E → E, FinitePiecewiseAffineOn h A ∧ InjOn h A ∧ h '' A = B ∧
          EqOn h id D ∧ EqOn h id (A \ g ⁻¹' interior (g '' T)) ∧
          (∀ x ∈ A, h x ∈ T ↔ x ∈ T) ∧
          (∃ G : (A ∩ T : Set E) ≃ₜ (B ∩ T : Set E),
            ∀ x : (A ∩ T : Set E), (G x : E) = h x) ∧
          ∀ (Z r : Set E), IsFinitePLBallPair (ℝ × ℝ) Z r → Z ⊆ A → Z ⊆ T →
            Disjoint (g '' r) (interior (g '' T)) →
            IsFinitePLBallPair (ℝ × ℝ) (h '' Z) r ∧ EqOn h id r ∧ h '' Z ⊆ T ∧
              (h '' Z) \ g ⁻¹' interior (g '' T) = Z \ g ⁻¹' interior (g '' T) ∧
              ((∀ x ∈ g '' Z,
                connectedComponentIn ((g '' A) ∩ (g '' T)) x = g '' Z) →
                ∀ x ∈ g '' (h '' Z),
                  connectedComponentIn ((g '' B) ∩ (g '' T)) x = g '' (h '' Z)) := by
  have hPK : MapsTo P.map Source (g '' K.space) :=
    fun _ hz => image_mono hTK (interior_subset (hP hz))
  obtain ⟨f,hf,hfi,hfK,hfg,hcarrier,hreplace⟩ :=
    P.exists_original_sphere_cap_replacement s he K hK hg hgi hPK hS k q hk
  refine ⟨f,hf,hfi,hfK,hfg,hcarrier,?_⟩
  intro b
  let D := K.space ∩ g ⁻¹' (s.map '' k b)
  let I := if b then Icc (0 : ℝ) (1/2) else Icc (-(1/2 : ℝ)) 0
  let t := if b then (1/2 : ℝ) else -(1/2)
  let C := (Disk ×ˢ {(0 : ℝ)}) ∪ (Rim ×ˢ I)
  let N := Disk ×ˢ {t}
  let A := D ∪ f '' C
  let B := D ∪ f '' N
  have hCsub : C ⊆ Source := by
    rintro ⟨x,u⟩ (⟨hx,hu⟩ | ⟨hx,hu⟩)
    · exact ⟨hx,by rw [show u = 0 from hu]; norm_num⟩
    · refine ⟨sphere_subset_closedBall hx,?_⟩
      cases b <;> dsimp [I] at hu <;> constructor <;> linarith [hu.1,hu.2]
  have hNsub : N ⊆ Source := by
    rintro ⟨x,u⟩ ⟨hx,hu⟩
    refine ⟨hx,?_⟩
    rw [show u = t from hu]
    cases b <;> norm_num [t]
  have hfint {z : V2 × ℝ} (hz : z ∈ Source) : g (f z) ∈ interior (g '' T) := by
    rw [hfg z hz]
    exact hP hz
  have hfT {z : V2 × ℝ} (hz : z ∈ Source) : f z ∈ T := by
    obtain ⟨x,hx,hxeq⟩ := interior_subset (hfint hz)
    exact (hgi (hTK hx) (hfK hz) hxeq) ▸ hx
  have hAK : A ⊆ K.space := union_subset inter_subset_left (by
    rintro _ ⟨z,hz,rfl⟩
    exact hfK (hCsub hz))
  have hBK : B ⊆ K.space := union_subset inter_subset_left (by
    rintro _ ⟨z,hz,rfl⟩
    exact hfK (hNsub hz))
  obtain ⟨_,_,_,H,hH,hHfix,hHD⟩ := hreplace b
  obtain ⟨h,hh,hval⟩ := hH
  have hval' (x : A) : h x = (H x : E) := (hval x).symm
  have hinj : InjOn h A := by
    intro x hx y hy hxy
    have heq : H ⟨x,hx⟩ = H ⟨y,hy⟩ := Subtype.ext
      ((hval ⟨x,hx⟩).trans (hxy.trans (hval ⟨y,hy⟩).symm))
    exact congrArg Subtype.val (H.injective heq)
  have hfull : h '' A = B := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [hval' ⟨x,hx⟩]
      exact (H ⟨x,hx⟩).property
    · intro y hy
      refine ⟨H.symm ⟨y,hy⟩,(H.symm ⟨y,hy⟩).property,?_⟩
      rw [hval',H.apply_symm_apply]
  have hfix : EqOn h id D := by
    intro x hx
    exact (hval' ⟨x,Or.inl hx⟩).trans (hHfix ⟨x,hx⟩)
  have hsupport : EqOn h id (A \ g ⁻¹' interior (g '' T)) := by
    rintro x ⟨hx,hn⟩
    rcases hx with hx | ⟨z,hz,rfl⟩
    · exact hfix hx
    · exact (hn (hfint (hCsub hz))).elim
  have hpres (x : E) (hx : x ∈ A) : h x ∈ T ↔ x ∈ T := by
    by_cases hxD : x ∈ D
    · rw [hfix hxD]
      rfl
    · have hxC : x ∈ f '' C := hx.resolve_left hxD
      have hxT : x ∈ T := by
        obtain ⟨z,hz,rfl⟩ := hxC
        exact hfT (hCsub hz)
      have hhD : h x ∉ D := by
        rw [hval' ⟨x,hx⟩]
        exact fun h => hxD ((hHD ⟨x,hx⟩).mp h)
      have hhN : h x ∈ f '' N := (hfull.subset (mem_image_of_mem h hx)).resolve_left hhD
      have hhT : h x ∈ T := by
        obtain ⟨z,hz,hzx⟩ := hhN
        exact hzx ▸ hfT (hNsub hz)
      exact iff_of_true hhT hxT
  obtain ⟨G,hG⟩ := H.exists_inter_restriction (fun x => by
    rw [hval x]
    exact hpres x x.property)
  refine ⟨h,hh,hinj,hfull,hfix,hsupport,hpres,
    ⟨G,fun x => (hG x).trans (hval ⟨x,x.property.1⟩)⟩,?_⟩
  intro Z r hZ hZA hZT hr
  have hrfix : EqOn h id r := by
    intro x hx
    exact hsupport ⟨hZA (hZ.1 hx),fun hn => disjoint_left.mp hr (mem_image_of_mem g hx) hn⟩
  have hrimage : h '' r = r := by
    exact (image_congr hrfix).trans (image_id r)
  have hnewdisk := hZ.image_of_subset hh hZA hinj
  rw [hrimage] at hnewdisk
  refine ⟨hnewdisk,hrfix,?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact (hpres x (hZA hx)).mpr (hZT hx)
  · apply Subset.antisymm
    · rintro y ⟨⟨x,hx,hxy⟩,hy⟩
      have hyD : y ∈ D := by
        rcases hfull.subset ⟨x,hZA hx,hxy⟩ with hyD | ⟨z,hz,hzy⟩
        · exact hyD
        · exact (hy (hzy ▸ hfint (hNsub hz))).elim
      have hxy' : x = y := hinj (hZA hx) (Or.inl hyD)
        (hxy.trans (hfix hyD).symm)
      exact ⟨hxy' ▸ hx,hy⟩
    · rintro x ⟨hx,hn⟩
      exact ⟨⟨x,hx,hsupport ⟨hZA hx,hn⟩⟩,hn⟩
  · exact transport_original_carrier_component K hK hg hgi hAK hBK hTK H
      hval' hpres hZA hZT

end PoincareConjecture.M76.OriginalDiskProduct
