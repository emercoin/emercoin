#ifndef JSON_SPIRIT_LEGACY_H
#define JSON_SPIRIT_LEGACY_H


/* -----------------------------------------------------------------------
 * -------------------------------- write --------------------------------
 * -----------------------------------------------------------------------
 */

template < class String_type >
String_type to_str( const char* c_str )
{
    String_type result;

    for( const char* p = c_str; *p != 0; ++p )
    {
        result += *p;
    }

    return result;
}

inline char to_hex_char( unsigned int c )
{
    assert( c <= 0xF );

    const char ch = static_cast< char >( c );

    if( ch < 10 ) return '0' + ch;

    return 'A' - 10 + ch;
}

template< class String_type >
String_type non_printable_to_string( unsigned int c )
{
    // Silence the warning: typedef ‘Char_type’ locally defined but not used [-Wunused-local-typedefs]
    // typedef typename String_type::value_type Char_type;

    String_type result( 6, '\\' );

    result[1] = 'u';

    result[ 5 ] = to_hex_char( c & 0x000F ); c >>= 4;
    result[ 4 ] = to_hex_char( c & 0x000F ); c >>= 4;
    result[ 3 ] = to_hex_char( c & 0x000F ); c >>= 4;
    result[ 2 ] = to_hex_char( c & 0x000F );

    return result;
}

template< typename Char_type, class String_type >
bool add_esc_char( Char_type c, String_type& s )
{
    switch( c )
    {
        case '"':  s += to_str< String_type >( "\\\"" ); return true;
        case '\\': s += to_str< String_type >( "\\\\" ); return true;
        case '\b': s += to_str< String_type >( "\\b"  ); return true;
        case '\f': s += to_str< String_type >( "\\f"  ); return true;
        case '\n': s += to_str< String_type >( "\\n"  ); return true;
        case '\r': s += to_str< String_type >( "\\r"  ); return true;
        case '\t': s += to_str< String_type >( "\\t"  ); return true;
    }

    return false;
}

template< class String_type >
String_type add_esc_chars( const String_type& s )
{
    typedef typename String_type::const_iterator Iter_type;
    typedef typename String_type::value_type     Char_type;

    String_type result;

    const Iter_type end( s.end() );

    for( Iter_type i = s.begin(); i != end; ++i )
    {
        const Char_type c( *i );

        if( add_esc_char( c, result ) ) continue;

        const wint_t unsigned_c( ( c >= 0 ) ? c : 256 + c );

        if( iswprint( unsigned_c ) )
        {
            result += c;
        }
        else
        {
            result += non_printable_to_string< String_type >( unsigned_c );
        }
    }

    return result;
}

/* ----------------------------------------------------------------------
 * -------------------------------- read --------------------------------
 * ----------------------------------------------------------------------
 */

template< class Char_type >
Char_type hex_to_num( const Char_type c )
{
    if( ( c >= '0' ) && ( c <= '9' ) ) return c - '0';
    if( ( c >= 'a' ) && ( c <= 'f' ) ) return c - 'a' + 10;
    if( ( c >= 'A' ) && ( c <= 'F' ) ) return c - 'A' + 10;
    return 0;
}

template< class Char_type, class Iter_type >
Char_type hex_str_to_char( Iter_type& begin )
{
    const Char_type c1( *( ++begin ) );
    const Char_type c2( *( ++begin ) );

    return ( hex_to_num( c1 ) << 4 ) + hex_to_num( c2 );
}

template< class Char_type, class Iter_type >
Char_type unicode_str_to_char( Iter_type& begin )
{
    const Char_type c1( *( ++begin ) );
    const Char_type c2( *( ++begin ) );
    const Char_type c3( *( ++begin ) );
    const Char_type c4( *( ++begin ) );

    return ( hex_to_num( c1 ) << 12 ) +
           ( hex_to_num( c2 ) <<  8 ) +
           ( hex_to_num( c3 ) <<  4 ) +
           hex_to_num( c4 );
}

template< class String_type >
void append_utf8( String_type& s, unsigned int cp )
{
    typedef typename String_type::value_type Char_type;

    if( cp < 0x80 )
    {
        s += static_cast< Char_type >( cp );
    }
    else if( cp < 0x800 )
    {
        s += static_cast< Char_type >( 0xC0 | ( cp >> 6 ) );
        s += static_cast< Char_type >( 0x80 | ( cp & 0x3F ) );
    }
    else if( cp < 0x10000 )
    {
        s += static_cast< Char_type >( 0xE0 | ( cp >> 12 ) );
        s += static_cast< Char_type >( 0x80 | ( ( cp >> 6 ) & 0x3F ) );
        s += static_cast< Char_type >( 0x80 | ( cp & 0x3F ) );
    }
    else
    {
        s += static_cast< Char_type >( 0xF0 | ( cp >> 18 ) );
        s += static_cast< Char_type >( 0x80 | ( ( cp >> 12 ) & 0x3F ) );
        s += static_cast< Char_type >( 0x80 | ( ( cp >> 6 ) & 0x3F ) );
        s += static_cast< Char_type >( 0x80 | ( cp & 0x3F ) );
    }
}

// Returns false for an escape that cannot be decoded (a surrogate without its pair).
template< class String_type >
bool append_esc_char_and_incr_iter( String_type& s,
                                    typename String_type::const_iterator& begin,
                                    typename String_type::const_iterator end )
{
    typedef typename String_type::value_type Char_type;

    const Char_type c2( *begin );

    switch( c2 )
    {
        case 't':  s += '\t'; break;
        case 'b':  s += '\b'; break;
        case 'f':  s += '\f'; break;
        case 'n':  s += '\n'; break;
        case 'r':  s += '\r'; break;
        case '\\': s += '\\'; break;
        case '/':  s += '/';  break;
        case '"':  s += '"';  break;
        case 'x':
        {
            if( end - begin >= 3 )  //  expecting "xHH..."
            {
                s += hex_str_to_char< Char_type >( begin );
            }
            break;
        }
        case 'u':
        {
            if( end - begin >= 5 )  //  expecting "uHHHH..."
            {
                // emercoin: json_spirit kept only the low byte of every \uHHHH. \u0000-\u00FF
                // stay single bytes: that is how the legacy writer escapes every non-ASCII byte,
                // and legacy clients send binary values back that way. Higher escapes only come
                // from standard JSON encoders (Python's json.dumps("\u0430") sends "\u0430"),
                // and the low byte silently corrupted that text ("0"), so they are decoded to UTF-8.
                const unsigned int cp = unicode_str_to_char< unsigned int >( begin );

                if( cp < 0x100 )
                {
                    s += static_cast< Char_type >( cp );
                }
                else if( cp >= 0xD800 && cp < 0xDC00 )  //  high surrogate, expecting "\uDC00-\uDFFF" next
                {
                    if( end - begin < 7 || *( begin + 1 ) != '\\' || *( begin + 2 ) != 'u' ) return false;
                    begin += 2;
                    const unsigned int low = unicode_str_to_char< unsigned int >( begin );
                    if( low < 0xDC00 || low >= 0xE000 ) return false;
                    append_utf8( s, 0x10000 + ( ( cp - 0xD800 ) << 10 ) + ( low - 0xDC00 ) );
                }
                else if( cp >= 0xDC00 && cp < 0xE000 )  //  low surrogate without a high one
                {
                    return false;
                }
                else
                {
                    append_utf8( s, cp );
                }
            }
            break;
        }
    }

    return true;
}

// Returns false if the string has an escape that cannot be decoded.
template< class String_type >
bool substitute_esc_chars( typename String_type::const_iterator begin,
                           typename String_type::const_iterator end,
                           String_type& result )
{
    typedef typename String_type::const_iterator Iter_type;

    result.clear();

    if( end - begin < 2 )
    {
        result.assign( begin, end );
        return true;
    }

    result.reserve( end - begin );

    const Iter_type end_minus_1( end - 1 );

    Iter_type substr_start = begin;
    Iter_type i = begin;

    for( ; i < end_minus_1; ++i )
    {
        if( *i == '\\' )
        {
            result.append( substr_start, i );

            ++i;  // skip the '\'

            if( !append_esc_char_and_incr_iter( result, i, end ) ) return false;

            substr_start = i + 1;
        }
    }

    result.append( substr_start, end );

    return true;
}

#endif // JSON_SPIRIT_LEGACY_H
