let length s =
  let rec aux i =
    if i >= String.length s then 0
    else
      let c = Uchar.utf_decode_uchar (String.get_utf_8_uchar s i) in
      let nc = Uchar.utf_8_byte_length c in
      1 + aux (i + nc)
  in
  aux 0

let make n glyph = String.concat "" (List.init n (fun _ -> glyph))
