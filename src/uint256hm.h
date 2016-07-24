/*
 * HashMap container for uint256 index -> value
 * Part of Emercoin project.
 *
 */

#ifndef EMC_UINT256HM_H
#define EMC_UINT256HM_H

#include "uint256.h"

// Container - debug version
template<class DATA>
  class uint256HashMap {
public:
    struct Data {
	Data() : next(-1) {}
	int32_t  next; // -1 = EMPTY; -2 = END
	uint256  key;
	DATA     value;
    };

   uint256HashMap() : m_head(-2), m_mask(0), m_allowed(0), m_data(NULL) {};
  ~uint256HashMap() { Set(0); };

  void Set(uint32_t size) {
    // delete data if exist and needed
    if(size == 0) {
      delete [] m_data;
      m_data = NULL;
      m_head = -2;
      return;
    }
    // Ignore 2nd Set()
    if(m_data)
      return;

    // compute size 2^n
    size += size >> 2; // Add 1/4 reserved 
    if((int32_t)size < 0)
	m_mask = 0x80000000;
    else
        for(m_mask = 64; m_mask < size; m_mask <<= 1);

    printf("uint256HashMap:Set(%u/%u) data=%u sz=%u\n", size, m_mask, sizeof(struct Data), m_mask * sizeof(struct Data));
    // allocate memory
    m_data = new Data[m_mask];
    // set allowed counter - Max population is 7/8
    m_allowed = m_mask - (m_mask >> 3);
    // set real mask
    m_mask--;
  } // Init

  uint32_t size() const {
      uint32_t x = m_mask + 1;
      x -= x >> 3; // orig allowed
      return x - m_allowed;
  }

  void clear() { // cleanup hashtable, no delete memory
      if(m_head == -2)
	  return;
      for(uint32_t i = 0; i <= m_mask; i++)
	  m_data[i].next = -1; // mark as free
      uint32_t x = m_mask + 1;
      m_allowed = x - (x >> 3);
      m_head = -2;
  }

   Data *Search(const uint256 &key) const {
     Data *rc = Lookup(key);
     return rc->next == -1? NULL : rc;
   } // Search

   Data *First() const {
       return m_head < 0? NULL : m_data + m_head;
   }

   Data *Next(Data *cur) const {
     // return cur->next < 0? NULL : m_data + cur->next;
     return (uint32_t)cur->next >= (uint32_t)-2? NULL : 
	 m_data + (cur->next & 0x7fffffff);
   } // Next

   // Mark for delete at next rehash
   void MarkDel(Data *cur) {
       cur->next |= 0x80000000;
   }

   Data *Insert(const uint256 &key, DATA &value) {
       if(m_allowed == 0) {
	 // rehash to 2xN table
         uint256HashMap<DATA> rehashed;
	 rehashed.Set(m_mask << 1);
	 Data *p;
	 for(p = First(); p != NULL; p = Next(p))
	   if(p->next >= -2)
	     rehashed.Insert(p->key, p->value);
         p = m_data;
	 m_data    = rehashed.m_data;
	 m_allowed = rehashed.m_allowed;
	 m_mask    = rehashed.m_mask;
	 m_head    = rehashed.m_head;
	 rehashed.m_data = p; // release current buffer
       } // reahsh

       Data *p = Lookup(key);
       if(p->next == -1) { // empty cell
         m_allowed--;
	 p->next = m_head;
	 m_head = p - m_data;
	 p->key = key;
       }
       if(p->next != -2)
         p->next &= 0x7fffffff; // Clear MarkDel, if exist
       p->value = value;
       return p;
   }

private:

  // Return pointer to the found cell, or to an empty cell
  Data *Lookup(const uint256 &key) const {
      const uint32_t *p = ((base_uint256)key).GetDataPtr();
      // Lowest part left; if changed, need modify indexes
      uint32_t pos  = p[0];
      uint32_t step = p[1] | 1; // odd step
      Data *rc;
      do {
	pos = (pos + step) & m_mask;
	rc = m_data + pos;
      } while((pos >= 0x7ffffffe) || (rc->next != -1 && memcmp(p, ((base_uint256)rc->key).GetDataPtr(), 256 / 8)));
      return rc;
  } // Lookup

  int32_t   m_head;
  uint32_t  m_mask;
  uint32_t  m_allowed;
  Data     *m_data;

}; // uint256HashMap

#endif



