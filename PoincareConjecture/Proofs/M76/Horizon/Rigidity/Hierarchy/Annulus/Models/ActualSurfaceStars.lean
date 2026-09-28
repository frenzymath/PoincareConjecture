import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.VertexStarChartRestriction
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence










set_option autoImplicit false
open Set Filter Geometry
open scoped Topology

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] [TopologicalSpace X]

theorem exists_transverse_hyperplane_coordinate_direction
    (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3)
    (hu : psi.contLinear u = 1) (hv : ell.contLinear v = 1)
    (huv : psi.contLinear v = 0)
    (a : V2 →ᴬ[ℝ] V3) (r : V3 →ᴬ[ℝ] V2)
    (har : LeftInvOn a r {z | ell z = 0}) (haz : ∀ z, ell (a z) = 0) :
    ∃ w : V2, (psi.comp a).contLinear w = 1 := by
  let w := u - ell.contLinear u • v
  have hw : ell.contLinear w = 0 := by simp [w, map_sub, map_smul, hv]
  have hwp : psi.contLinear w = 1 := by simp [w, map_sub, map_smul, hu, huv]
  have hz : ell (w + a 0) = 0 := by
    have h := ell.toAffineMap.map_vadd (a 0) w
    change ell (w + a 0) = ell.contLinear w + ell (a 0) at h
    simpa only [hw, haz, add_zero] using h
  have hp : psi (w + a 0) - psi (a 0) = 1 := by
    have h := psi.toAffineMap.map_vadd (a 0) w
    change psi (w + a 0) = psi.contLinear w + psi (a 0) at h
    rw [h, hwp]
    ring
  refine ⟨r (w + a 0) - r (a 0), ?_⟩
  have h := (psi.comp a).toAffineMap.linearMap_vsub (r (w + a 0)) (r (a 0))
  change (psi.comp a).contLinear (r (w + a 0) - r (a 0)) =
    psi (a (r (w + a 0))) - psi (a (r (a 0))) at h
  rw [har hz, har (haz 0), hp] at h
  exact h

theorem exists_surface_star_image_patch
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {S : Set X} (H : K.space ≃ₜ S) (g : E → X)
    (hH : ∀ z : K.space, (H z : X) = g z)
    {p : E} (hp : p ∈ K.vertices) (T : OpenPartialHomeomorph X V3)
    (hsource : MapsTo g (K.closedStar p).space T.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => T (g z)))
    (ell : V3 →ᴬ[ℝ] ℝ) (a : V2 →ᴬ[ℝ] V3) (r : V3 →ᴬ[ℝ] V2)
    (hra : Function.LeftInverse r a) (har : LeftInvOn a r {z | ell z = 0})
    (haz : ∀ z, ell (a z) = 0) (Q : Set V2)
    (hlocal : ∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ r (T y) ∈ Q) :
    let f : E → V2 := fun z => r (T (g z))
    (K.closedStar p).AffineOnFaces f ∧ InjOn f (K.closedStar p).space ∧
    ∃ V : Set V2, IsOpen V ∧ f p ∈ V ∧
      V ∩ Q ⊆ f '' (K.closedStar p).space ∧ f '' (K.closedStar p).space ⊆ Q := by
  classical
  let D : Set K.space := Subtype.val ⁻¹' (K.closedStar p).space
  have hsub : (K.closedStar p).space ⊆ K.space :=
    SimplicialComplex.space_subset_of_le (fun _ hs => hs.1)
  have hpK := K.vertices_subset_space hp
  let z : K.space := ⟨p, hpK⟩
  have hD : D ∈ 𝓝 z := by
    rw [show D = Subtype.val ⁻¹' (K.closedFaceStar {p}).space from by
      rw [K.closedFaceStar_singleton_eq_closedStar]]
    exact K.closedFaceStar_mem_nhds_of_intrinsicInterior hK hp z (by
      simp [z, intrinsicInterior_singleton])
  have hpstar : p ∈ (K.closedStar p).space := (show z ∈ D from mem_of_mem_nhds hD)
  have hgS (x : E) (hx : x ∈ K.space) : g x ∈ S := by
    rw [← hH ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hzero (x : E) (hx : x ∈ (K.closedStar p).space) : ell (T (g x)) = 0 :=
    ((hlocal _ (hsource hx)).mp (hgS x (hsub hx))).1
  have hHD := H.isOpenMap.image_mem_nhds hD
  obtain ⟨W, hW, hWS⟩ := (mem_nhds_subtype S (H z) (H '' D)).mp hHD
  obtain ⟨O, hOW, hO, hpO⟩ := mem_nhds_iff.mp hW
  let V : Set V2 := a ⁻¹' (T '' (T.source ∩ O))
  refine ⟨hface.postcomp r, ?_, V, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hT : T (g x) = T (g y) := by
      rw [← har (hzero x hx), ← har (hzero y hy)]
      exact congrArg a hxy
    have hg := T.injOn (hsource hx) (hsource hy) hT
    have hHH : H ⟨x, hsub hx⟩ = H ⟨y, hsub hy⟩ := by
      apply Subtype.ext
      simpa only [hH] using hg
    exact congrArg Subtype.val (H.injective hHH)
  · exact (T.isOpen_image_source_inter hO).preimage a.continuous
  · change a (r (T (g p))) ∈ T '' (T.source ∩ O)
    rw [har (hzero p hpstar)]
    exact ⟨g p, ⟨hsource hpstar, by simpa only [hH] using hpO⟩, rfl⟩
  · intro w hw
    obtain ⟨y, ⟨hyT, hyO⟩, hya⟩ := hw.1
    have hyS : y ∈ S := (hlocal y hyT).mpr ⟨by rw [hya]; exact haz w, by
      rw [hya, hra]; exact hw.2⟩
    obtain ⟨x, hxD, hxH⟩ := hWS (show (⟨y, hyS⟩ : S) ∈ Subtype.val ⁻¹' W from hOW hyO)
    refine ⟨x, hxD, ?_⟩
    have hxy : g x = y := by
      rw [← hH x]
      exact congrArg Subtype.val hxH
    change r (T (g x)) = w
    rw [hxy, hya, hra]
  · rintro w ⟨x, hx, rfl⟩
    exact ((hlocal _ (hsource hx)).mp (hgS x (hsub hx))).2

theorem marked_surface_planar_halfspace_stars
    (K B : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {S M : Set X} (H : K.space ≃ₜ S) (g : E → X)
    (hH : ∀ z : K.space, (H z : X) = g z)
    (hB : ∀ z ∈ K.space, g z ∈ M ↔ z ∈ B.space)
    (hcharts : ∀ p ∈ K.vertices, ∃ T : OpenPartialHomeomorph X V3,
      MapsTo g (K.closedStar p).space T.source ∧
      (K.closedStar p).AffineOnFaces (fun z => T (g z)) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source M) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ M ↔ psi (T y) = 0)) :
    ∀ p ∈ K.vertices, ∃ (f : E → V2) (V : Set V2),
      (K.closedStar p).AffineOnFaces f ∧ InjOn f (K.closedStar p).space ∧
      IsOpen V ∧ f p ∈ V ∧
      ((V ⊆ f '' (K.closedStar p).space ∧ Disjoint (K.closedStar p).space B.space) ∨
        ∃ (ell : V2 →ᴬ[ℝ] ℝ) (v : V2), ell.contLinear v = 1 ∧
          V ∩ {z | 0 ≤ ell z} ⊆ f '' (K.closedStar p).space ∧
          f '' (K.closedStar p).space ⊆ {z | 0 ≤ ell z} ∧
          ∀ x ∈ (K.closedStar p).space, x ∈ B.space ↔ ell (f x) = 0) := by
  intro p hp
  obtain ⟨T, hsource, hface, hkind⟩ := hcharts p hp
  have hsub : (K.closedStar p).space ⊆ K.space :=
    SimplicialComplex.space_subset_of_le (fun _ hs => hs.1)
  have hgS (x : E) (hx : x ∈ K.space) : g x ∈ S := by
    rw [← hH ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  rcases hkind with ⟨ell, v, hv, hlocal, hdis⟩ |
    ⟨ell, psi, u, v, hu, hv, huv, hlocal, hmark⟩
  · have hell : ell.toAffineMap.linear ≠ 0 := by
      intro h
      have hval : ell.toAffineMap.linear v = 1 := hv
      rw [h, LinearMap.zero_apply] at hval
      exact zero_ne_one hval
    obtain ⟨a, r, hra, har, haz⟩ :=
      ell.toAffineMap.exists_zeroLevel_coordinates (F := V2) hell (by simp)
    obtain ⟨hf, hi, V, hV, hpV, hpatch, _⟩ :=
      exists_surface_star_image_patch K hK H g hH hp T hsource hface ell a r hra har haz
        univ (by intro y hy; simpa only [mem_univ, and_true] using hlocal y hy)
    refine ⟨fun z => r (T (g z)), V, hf, hi, hV, hpV, Or.inl ⟨?_, ?_⟩⟩
    · simpa only [inter_univ] using hpatch
    · apply disjoint_left.mpr
      intro x hx hxB
      exact disjoint_left.mp hdis (hsource hx) ((hB x (hsub hx)).mpr hxB)
  · have hell : ell.toAffineMap.linear ≠ 0 := by
      intro h
      have hval : ell.toAffineMap.linear v = 1 := hv
      rw [h, LinearMap.zero_apply] at hval
      exact zero_ne_one hval
    obtain ⟨a, r, hra, har, haz⟩ :=
      ell.toAffineMap.exists_zeroLevel_coordinates (F := V2) hell (by simp)
    obtain ⟨w, hw⟩ := exists_transverse_hyperplane_coordinate_direction ell psi u v
      hu hv huv a r har haz
    have hlocal' (y : X) (hy : y ∈ T.source) :
        y ∈ S ↔ ell (T y) = 0 ∧ r (T y) ∈ {z | 0 ≤ (psi.comp a) z} := by
      rw [hlocal y hy]
      constructor <;> intro h
      · exact ⟨h.1, by change 0 ≤ psi (a (r (T y))); rw [har h.1]; exact h.2⟩
      · refine ⟨h.1, ?_⟩
        have hh : 0 ≤ psi (a (r (T y))) := h.2
        simpa only [har h.1] using hh
    obtain ⟨hf, hi, V, hV, hpV, hpatch, hhalf⟩ :=
      exists_surface_star_image_patch K hK H g hH hp T hsource hface ell a r hra har haz
        {z | 0 ≤ (psi.comp a) z} hlocal'
    refine ⟨fun z => r (T (g z)), V, hf, hi, hV, hpV,
      Or.inr ⟨psi.comp a, w, hw, hpatch, hhalf, ?_⟩⟩
    intro x hx
    have hz := ((hlocal (g x) (hsource hx)).mp (hgS x (hsub hx))).1
    change x ∈ B.space ↔ psi (a (r (T (g x)))) = 0
    rw [har hz, ← hmark (g x) (hsource hx)]
    exact (hB x (hsub hx)).symm

end PoincareConjecture.M76
