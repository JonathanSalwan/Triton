
#ifndef   __SNAPSHOTENGINE_H__
#define   __SNAPSHOTENGINE_H__

#include "pin.H"


class SnapshotEngine{
 
  private: 
    /* I/O memory monitoring for snapshot */
    /* item1: memory address              */
    /* item2: byte                        */
    std::list< std::pair<UINT64, UINT8> > memory;

  public:
    SnapshotEngine();
    ~SnapshotEngine();

};

#endif     /* !__SNAPSHOTENGINE_H__ */

