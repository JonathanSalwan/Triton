#ifndef _TRIGGER_H_
#define _TRIGGER_H_

class Trigger {
  public:
    // Build a trigger set in the OFF state.
    Trigger();

    // Switch the trigger.
    void toggle();

    // Return true if the switch is ON, false otherwise.
    bool getState();

  private:
    bool _state;
};

#endif // _TRIGGER_H_
